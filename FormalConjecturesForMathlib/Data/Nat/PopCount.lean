/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

module

public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Group.List
public import Mathlib.Data.Nat.Digits.Lemmas

@[expose] public section

/-!
# A kernel-friendly population count

`popCount` counts the set bits of a natural number below `2 ^ 672` using the standard
SWAR (SIMD-within-a-register) folding trick: adjacent `w`-bit fields are added in parallel
by masking a value against its own `w`-bit right shift, doubling the field width at each of
the four stages, and the sixteen-bit totals are finally summed by a single reduction modulo
`65535`. Every step is a `Nat` bitwise operation on a single big number, so `decide +kernel`
can evaluate it.

*References*:
- [Wikipedia, Hamming weight](https://en.wikipedia.org/wiki/Hamming_weight)

## Main definitions

* `popCount`: the number of set bits of a natural number below `2 ^ 672`.

## Main statements

* `popCount_eq_sum`: `popCount z` is the number of set bits of `z`, for every `z < 2 ^ 672`.
* `popCount_eq_sum_of_lt`: the same count taken over any range wide enough to contain the bits.

-/

namespace Nat

/-- `k` copies of the chunk `c` (each `w` bits wide, `c < 2 ^ w`), least significant first. -/
def repMask (c w : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => c + repMask c w k * 2 ^ w

/-- Sum adjacent pairs of a list. -/
private def pairs : List ℕ → List ℕ
  | [] => []
  | [_] => []
  | a :: b :: t => (a + b) :: pairs t

@[simp] private theorem pairs_cons₂ (a b : ℕ) (t : List ℕ) :
    pairs (a :: b :: t) = (a + b) :: pairs t := rfl

private theorem sum_pairs (l : List ℕ) (hl : 2 ∣ l.length) : (pairs l).sum = l.sum := by
  induction l using pairs.induct with
  | case1 => rfl
  | case2 a => simp at hl
  | case3 a b t ih =>
    have ht : 2 ∣ t.length := by simp only [List.length_cons] at hl; omega
    simp only [pairs_cons₂, List.sum_cons, ih ht]
    omega

private theorem pairs_le (l : List ℕ) (c : ℕ) (hl : ∀ x ∈ l, x ≤ c) :
    ∀ x ∈ pairs l, x ≤ 2 * c := by
  induction l using pairs.induct with
  | case1 => nofun
  | case2 a => nofun
  | case3 a b t ih =>
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · have := hl a (.head _); have := hl b (.tail _ (.head _)); omega
    · exact ih (fun y hy ↦ hl y (.tail _ (.tail _ hy))) x hx

/-- Bitwise `and` distributes over a split at a `B = 2 ^ w` digit boundary. -/
theorem add_mul_and_add_mul (B w a b c d : ℕ) (hB : B = 2 ^ w) (ha : a < B) (hc : c < B) :
    (a + B * b) &&& (c + B * d) = (a &&& c) + B * (b &&& d) := by
  subst hB
  have hac : a &&& c < 2 ^ w := lt_of_le_of_lt Nat.and_le_left ha
  apply Nat.eq_of_testBit_eq
  intro i
  rw [Nat.add_comm a, Nat.add_comm c, Nat.add_comm (a &&& c), Nat.testBit_and,
    Nat.testBit_two_pow_mul_add b ha i, Nat.testBit_two_pow_mul_add d hc i,
    Nat.testBit_two_pow_mul_add (b &&& d) hac i]
  by_cases h : i < w <;> simp [h, Nat.testBit_and]

private theorem repMask_succ (c w k : ℕ) : repMask c w (k + 1) = c + 2 ^ w * repMask c w k := by
  rw [repMask]; ring

private theorem add_mul_lt_mul_self {a b B : ℕ} (ha : a < B) (hb : b < B) :
    a + B * b < B * B := by
  have : B * b + B ≤ B * B :=
    calc B * b + B = B * (b + 1) := by ring
      _ ≤ B * B := Nat.mul_le_mul_left B hb
  omega

private theorem add_mul_and_sub_one {B w x : ℕ} (hB : B = 2 ^ w) (hx : x < B) (y : ℕ) :
    (x + B * y) &&& (B - 1) = x := by
  subst hB
  rw [Nat.and_two_pow_sub_one_eq_mod, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hx]

private theorem shiftRight_add_mul_add {B w a b T : ℕ} (hB : B = 2 ^ w) (ha : a < B) :
    (a + B * b + B * B * T) >>> w = b + B * (T % B) + B * B * (T / B) := by
  have hBpos : 0 < B := hB ▸ Nat.two_pow_pos w
  rw [Nat.shiftRight_eq_div_pow, ← hB]
  have h1 : a + B * b + B * B * T = a + B * (b + B * T) := by ring
  have h2 : (a + B * (b + B * T)) / B = b + B * T := by
    rw [Nat.add_mul_div_left _ _ hBpos, Nat.div_eq_of_lt ha, Nat.zero_add]
  have h3 : B * T = B * (B * (T / B)) + B * (T % B) := by
    conv_lhs => rw [← Nat.div_add_mod T B]
    ring
  rw [h1, h2, h3]; ring

/-- The generic SWAR folding step, with the base `B = 2 ^ w` kept opaque. -/
private theorem swar_step (w B : ℕ) (hB : B = 2 ^ w) (l : List ℕ) (hl : ∀ x ∈ l, x < B)
    (k : ℕ) (hk : l.length = 2 * k) :
    (Nat.ofDigits B l &&& repMask (B - 1) (2 * w) k) +
        ((Nat.ofDigits B l >>> w) &&& repMask (B - 1) (2 * w) k) =
      Nat.ofDigits (B * B) (pairs l) := by
  have hpow : (2 : ℕ) ^ (2 * w) = B * B := by rw [two_mul, pow_add, hB]
  have hBpos : 0 < B := hB ▸ Nat.two_pow_pos w
  have hmaskstep : ∀ j, repMask (B - 1) (2 * w) (j + 1)
      = (B - 1) + B * B * repMask (B - 1) (2 * w) j := by
    intro j; rw [repMask_succ, hpow]
  have hsplit : ∀ a b c d : ℕ, a < B * B → c < B * B →
      (a + B * B * b) &&& (c + B * B * d) = (a &&& c) + B * B * (b &&& d) :=
    fun a b c d ha hc ↦ add_mul_and_add_mul (B * B) (2 * w) a b c d hpow.symm ha hc
  have hmasklt : B - 1 < B * B := by
    have : B ≤ B * B := Nat.le_mul_of_pos_left B hBpos
    omega
  induction l using pairs.induct generalizing k with
  | case1 => simp [pairs, Nat.ofDigits]
  | case2 a => simp only [List.length_cons, List.length_nil] at hk; omega
  | case3 a0 a1 t ih =>
    have hlen : t.length + 2 = 2 * k := by simp only [List.length_cons] at hk; omega
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have ha0 : a0 < B := hl a0 (.head _)
    have ha1 : a1 < B := hl a1 (.tail _ (.head _))
    have ht : ∀ x ∈ t, x < B := fun x hx ↦ hl x (.tail _ (.tail _ hx))
    set T := Nat.ofDigits B t
    have hTlow : T % B < B := Nat.mod_lt _ hBpos
    have hz : Nat.ofDigits B (a0 :: a1 :: t) = (a0 + B * a1) + B * B * T := by
      rw [Nat.ofDigits_cons, Nat.ofDigits_cons]; ring
    have hTdiv : T / B = T >>> w := by rw [Nat.shiftRight_eq_div_pow, hB]
    have hIH := ih ht k' (by omega)
    rw [hz, pairs_cons₂, Nat.ofDigits_cons, shiftRight_add_mul_add hB ha0, hmaskstep k',
      hsplit _ _ _ _ (add_mul_lt_mul_self ha0 ha1) hmasklt,
      hsplit _ _ _ _ (add_mul_lt_mul_self ha1 hTlow) hmasklt,
      add_mul_and_sub_one hB ha0 a1, add_mul_and_sub_one hB ha1 (T % B), hTdiv, ← hIH]
    ring

/-- Casting out `b`'s: in base `b + 1`, reducing mod `b` sums the digits. This is the final
fold of the pipeline, where `b = 65535` and the digits are the sixteen-bit lane totals. -/
theorem ofDigits_succ_mod {b : ℕ} (hb : 1 < b) (l : List ℕ) (hsum : l.sum < b) :
    Nat.ofDigits (b + 1) l % b = l.sum := by
  rw [Nat.ofDigits_mod, Nat.add_mod_left, Nat.mod_eq_of_lt hb]
  simp only [ofDigits_one, Nat.mod_eq_of_lt hsum]

/-- `pairs` halves the length of an even-length list. -/
private theorem length_pairs (l : List ℕ) (k : ℕ) (hk : l.length = 2 * k) :
    (pairs l).length = k := by
  induction l using pairs.induct generalizing k with
  | case1 => simp only [pairs, List.length_nil] at hk ⊢; omega
  | case2 a => simp only [List.length_cons, List.length_nil] at hk; omega
  | case3 a b t ih =>
    have ht : t.length + 2 = 2 * k := by simp only [List.length_cons] at hk; omega
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    simp only [pairs_cons₂, List.length_cons, ih (k := k') (by omega)]

/-- The SWAR popcount pipeline for 672-bit inputs, on plain `ℕ`. -/
def popCount (z : ℕ) : ℕ :=
  let x1 := (z &&& repMask 1 2 336) + ((z >>> 1) &&& repMask 1 2 336)
  let x2 := (x1 &&& repMask 3 4 168) + ((x1 >>> 2) &&& repMask 3 4 168)
  let x4 := (x2 &&& repMask 15 8 84) + ((x2 >>> 4) &&& repMask 15 8 84)
  let x8 := (x4 &&& repMask 255 16 42) + ((x4 >>> 8) &&& repMask 255 16 42)
  x8 % 65535

/-- `popCount` really is the bit-count, for any 672-bit-wide bit list. -/
private theorem popCount_ofDigits (l : List ℕ) (hl : ∀ x ∈ l, x ≤ 1)
    (hlen : l.length = 672) :
    popCount (Nat.ofDigits 2 l) = l.sum := by
  have hsum : l.sum ≤ 672 := by
    simpa [hlen] using List.sum_le_card_nsmul l 1 hl
  -- The four folding stages
  have h1 := swar_step 1 2 (by rfl) l (fun x hx ↦ by have := hl x hx; omega) 336 (by omega)
  have hl1 : ∀ x ∈ pairs l, x < 4 := fun x hx ↦ by have := pairs_le l 1 hl x hx; omega
  have hlen1 : (pairs l).length = 336 := length_pairs l 336 (by omega)
  have h2 := swar_step 2 4 (by rfl) (pairs l) hl1 168 (by omega)
  have hl2 : ∀ x ∈ pairs (pairs l), x < 16 := fun x hx ↦ by
    have := pairs_le (pairs l) 3 (fun y hy ↦ by have := hl1 y hy; omega) x hx; omega
  have hlen2 : (pairs (pairs l)).length = 168 := length_pairs _ 168 (by omega)
  have h3 := swar_step 4 16 (by rfl) (pairs (pairs l)) hl2 84 (by omega)
  have hl3 : ∀ x ∈ pairs (pairs (pairs l)), x < 256 := fun x hx ↦ by
    have := pairs_le _ 15 (fun y hy ↦ by have := hl2 y hy; omega) x hx; omega
  have hlen3 : (pairs (pairs (pairs l))).length = 84 := length_pairs _ 84 (by omega)
  have h4 := swar_step 8 256 (by rfl) (pairs (pairs (pairs l))) hl3 42 (by omega)
  simp only [Nat.reduceSub, Nat.reduceMul] at h1 h2 h3 h4
  -- The sums are preserved by each fold
  have s1 : (pairs l).sum = l.sum := sum_pairs l (by omega)
  have s2 : (pairs (pairs l)).sum = l.sum := (sum_pairs _ (by omega)).trans s1
  have s3 : (pairs (pairs (pairs l))).sum = l.sum := (sum_pairs _ (by omega)).trans s2
  have s4 : (pairs (pairs (pairs (pairs l)))).sum = l.sum := (sum_pairs _ (by omega)).trans s3
  rw [popCount, h1, h2, h3, h4, ofDigits_succ_mod (by omega) _ (by omega), s4]

/-! ### From `popCount` to bit counts -/

/-- The `n` low bits of `z`, least significant first. -/
private abbrev lowBits (n z : ℕ) : List ℕ := List.ofFn fun i : Fin n ↦ z / 2 ^ (i : ℕ) % 2

private theorem lowBits_succ (n z : ℕ) : lowBits (n + 1) z = (z % 2) :: lowBits n (z / 2) := by
  rw [lowBits, List.ofFn_succ]
  simp [lowBits, Nat.div_div_eq_div_mul, pow_succ']

private theorem ofDigits_lowBits (n z : ℕ) : Nat.ofDigits 2 (lowBits n z) = z % 2 ^ n := by
  induction n generalizing z with
  | zero => simp [lowBits, Nat.mod_one]
  | succ n ih => rw [lowBits_succ, Nat.ofDigits_cons, ih, pow_succ', Nat.mod_mul]

/-- `popCount` counts the set bits of any `z < 2 ^ 672`. -/
theorem popCount_eq_sum (z : ℕ) (hz : z < 2 ^ 672) :
    popCount z = ∑ i ∈ Finset.range 672, z / 2 ^ i % 2 := by
  calc popCount z
      = popCount (Nat.ofDigits 2 (lowBits 672 z)) := by
        rw [ofDigits_lowBits, Nat.mod_eq_of_lt hz]
    _ = (lowBits 672 z).sum :=
        popCount_ofDigits _ (by rw [lowBits, List.forall_mem_ofFn_iff]; intro j; omega)
          List.length_ofFn
    _ = ∑ i ∈ Finset.range 672, z / 2 ^ i % 2 := by
        rw [List.sum_ofFn, Fin.sum_univ_eq_sum_range (fun i ↦ z / 2 ^ i % 2) 672]

-- `w` is kept a variable so that callers at a fixed width never evaluate `2 ^ w`.
/-- `popCount` counts the set bits of `z` over any range wide enough to contain them. -/
theorem popCount_eq_sum_of_lt {z w : ℕ} (hz : z < 2 ^ w) (hw : w ≤ 672) :
    popCount z = ∑ i ∈ Finset.range w, z / 2 ^ i % 2 := by
  have h672 : popCount z = ∑ i ∈ Finset.range 672, z / 2 ^ i % 2 := by
    refine popCount_eq_sum _ (lt_of_lt_of_le hz ?_)
    gcongr
    omega
  rw [h672, Finset.range_eq_Ico, ← Finset.sum_Ico_consecutive _ (Nat.zero_le w) hw,
    ← Finset.range_eq_Ico]
  have : ∑ i ∈ Finset.Ico w 672, z / 2 ^ i % 2 = 0 :=
    Finset.sum_eq_zero fun i hi ↦ by
      rw [Nat.div_eq_of_lt (hz.trans_le
        (Nat.pow_le_pow_right Nat.zero_lt_two (Finset.mem_Ico.mp hi).1)), Nat.zero_mod]
  omega

end Nat
