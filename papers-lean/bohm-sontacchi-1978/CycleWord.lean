/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import Collatz.Affine
import Mathlib.Data.List.Rotate

/-!
# Parity words and the Böhm–Sontacchi cycle equation

A finite orbit of the Terras map `T` is recorded by its parity word, the list of parities of its
points. In this file we attach to every parity word `w` a numerator `rhoW w` and prove the
Böhm–Sontacchi correspondence: a point `m` of a `T`-cycle of length `L` with `k` odd steps satisfies
`(2^L − 3^k) · m = rhoW (parityWord L m)`, and conversely every word `w` with `3^c < 2^L` whose
numerator is divisible by `2^L − 3^c` comes from a periodic point.

As a consequence, the absence of nontrivial cycles is equivalent to a statement about words alone,
`CycleDivStatement`, which mentions no dynamics. We also give the classical bounds on `rhoW w`.

## Main definitions

- `rhoW w`: the word numerator `Σ_i 3^{c-1-i} 2^{e_i}`, where `e_0 < ⋯ < e_{c-1}` are the
  positions of `true` in `w`.
- `parityWord j n`: the parities of `n, T n, …, T^{j-1} n`.
- `CycleDivStatement`: for every word with `3^c < 2^L`, if `2^L − 3^c ∣ rhoW w` then the quotient
  is at most `2`.
- `NoNontrivialCycles`: every positive `C`-cycle point is `1`, `2` or `4`.

## Main results

- `rho_eq_rhoW`: the Terras remainder `rho j n` is the numerator of the parity word of `n`.
- `cycle_eq_word`: a `T`-cycle `T^[L] m = m` satisfies `(2^L − 3^k) · m = rhoW (parityWord L m)`.
- `cycle_of_word`, `parityWord_cycle_of_word`: if `3^c < 2^L` and `2^L − 3^c ∣ rhoW w`, then
  `rhoW w / (2^L − 3^c)` is a `T`-periodic point with parity word `w`.
- `noNontrivialCycles_iff_cycleDiv`: `NoNontrivialCycles ↔ CycleDivStatement`.
- `rhoW_lower`, `rhoW_upper`: `3^c ≤ rhoW w + 2^c` and `rhoW w + 2^L ≤ 3^c · 2^{L−c}`.
- `cycle_point_lower`, `cycle_point_upper`: the corresponding bounds for every point of a cycle.

## Notation

For a word `w`, `L = w.length`, `c = w.count true`, and `D(w) = 2^L − 3^c` (natural-number
subtraction, used under the hypothesis `3^c < 2^L`).

## References

- C. Böhm, G. Sontacchi, *On the existence of cycles of given length in integer sequences like
  `x_{n+1} = x_n/2` if `x_n` even, and `x_{n+1} = 3x_n + 1` otherwise*, Atti Accad. Naz. Lincei
  Rend. 64 (1978), 260–264.
-/

namespace Collatz

open CollatzProof

/-! ### The word numerator and parity words -/

/-- The word numerator: `rhoW [] = 0` and `rhoW (b :: u) = 2 · rhoW u + [b] · 3^{#true u}`;
equivalently `Σ_i 3^{c-1-i} 2^{e_i}` over the positions `e_0 < ⋯ < e_{c-1}` of `true`. -/
def rhoW : List Bool → ℕ
  | [] => 0
  | b :: w => 2 * rhoW w + (if b then 3 ^ w.count true else 0)

/-- `parityWord j n` is the list `[n odd, T n odd, …, T^{j-1} n odd]`. -/
def parityWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, n => decide (n % 2 = 1) :: parityWord j (T n)

theorem count_true_cons (b : Bool) (u : List Bool) :
    (b :: u).count true = u.count true + (if b then 1 else 0) := by
  cases b <;> simp

/-- Moving the first letter to the end preserves the number of `true`s. -/
theorem count_true_append_singleton (b : Bool) (u : List Bool) :
    (u ++ [b]).count true = (b :: u).count true := by
  cases b <;> simp [List.count_append]

/-- Moving the first letter to the end preserves the length. -/
theorem length_append_singleton' (b : Bool) (u : List Bool) :
    (u ++ [b]).length = (b :: u).length := by simp

theorem length_parityWord (j n : ℕ) : (parityWord j n).length = j := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih => simp [parityWord, ih]

/-- The number of `true`s in the parity word is the number of odd steps. -/
theorem count_parityWord (j n : ℕ) : (parityWord j n).count true = oddSteps j n := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    rw [parityWord, count_true_cons, ih, oddSteps]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

/-- The Terras remainder is the numerator of the parity word. -/
theorem rho_eq_rhoW (j n : ℕ) : rho j n = rhoW (parityWord j n) := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    rw [parityWord, rhoW, rho, ih, count_parityWord]
    rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h]

/-- Appending an odd step: `rhoW (w ++ [true]) = 3 · rhoW w + 2^{|w|}`. -/
theorem rhoW_append_true (w : List Bool) : rhoW (w ++ [true]) = 3 * rhoW w + 2 ^ w.length := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.cons_append, rhoW, rhoW, ih, count_true_append_singleton, count_true_cons]
    cases b <;> simp [pow_succ] <;> ring

/-- Appending an even step does not change the numerator. -/
theorem rhoW_append_false (w : List Bool) : rhoW (w ++ [false]) = rhoW w := by
  induction w with
  | nil => rfl
  | cons b w ih =>
    rw [List.cons_append, rhoW, rhoW, ih, count_true_append_singleton, count_true_cons]
    simp

/-! ### The forward cycle equation -/

/-- **Böhm–Sontacchi cycle equation.** A `T`-cycle `T^[L] m = m` satisfies
`(2^L − 3^k) · m = rhoW (parityWord L m)`, where `k = oddSteps L m`. -/
theorem cycle_eq_word {m L : ℕ} (h : T^[L] m = m) :
    (2 ^ L - 3 ^ oddSteps L m) * m = rhoW (parityWord L m) := by
  rw [← rho_eq_rhoW, Nat.sub_mul]
  have := cycle_equation h
  omega

/-! ### The converse -/

/-- One step of the converse, both conclusions at once; see `word_step_mod_two` and `word_step`. -/
private theorem word_step_aux {b : Bool} {u : List Bool} {n : ℕ}
    (hlt : 3 ^ (b :: u).count true < 2 ^ (b :: u).length)
    (h : (2 ^ (b :: u).length - 3 ^ (b :: u).count true) * n = rhoW (b :: u)) :
    n % 2 = (if b then 1 else 0) ∧
    (2 ^ (b :: u).length - 3 ^ (b :: u).count true) * T n = rhoW (u ++ [b]) := by
  generalize hD : 2 ^ (b :: u).length - 3 ^ (b :: u).count true = D at h ⊢
  have hDe : D + 3 ^ (b :: u).count true = 2 ^ (b :: u).length := by omega
  have h2L : 2 ^ (b :: u).length = 2 * 2 ^ u.length := by
    rw [List.length_cons, pow_succ]; ring
  have h3 := three_pow_mod_two ((b :: u).count true)
  have h3' := three_pow_mod_two (u.count true)
  have hDodd : D % 2 = 1 := by omega
  have hmod : D * n % 2 = n % 2 := by
    rw [Nat.mul_mod, hDodd, one_mul, Nat.mod_mod]
  have e2 : D * n = D * (n % 2) + 2 * (D * (n / 2)) := by
    conv_lhs => rw [← Nat.mod_add_div n 2]
    ring
  rw [rhoW] at h
  cases b with
  | false =>
    simp only [Bool.false_eq_true, ite_false, add_zero] at h ⊢
    have hn : n % 2 = 0 := by omega
    refine ⟨hn, ?_⟩
    rw [rhoW_append_false, T_of_even hn]
    rw [hn, mul_zero, zero_add] at e2
    omega
  | true =>
    simp only [ite_true] at h ⊢
    have hn : n % 2 = 1 := by omega
    refine ⟨hn, ?_⟩
    rw [rhoW_append_true]
    have hT : 2 * T n = 3 * n + 1 := by rw [T_of_odd hn]; omega
    have key : 2 * (D * T n) = 3 * (D * n) + D := by
      rw [show 2 * (D * T n) = D * (2 * T n) by ring, hT]; ring
    simp only [count_true_cons, ite_true, pow_succ] at hDe
    omega

/-- If `D(w) · n = rhoW w` for `w = b :: u` with `3^c < 2^L`, then the parity of `n` is `b`. -/
theorem word_step_mod_two {b : Bool} {u : List Bool} {n : ℕ}
    (hlt : 3 ^ (b :: u).count true < 2 ^ (b :: u).length)
    (h : (2 ^ (b :: u).length - 3 ^ (b :: u).count true) * n = rhoW (b :: u)) :
    n % 2 = (if b then 1 else 0) :=
  (word_step_aux hlt h).1

/-- If `D(w) · n = rhoW w` for `w = b :: u` with `3^c < 2^L`, then `D(w) · T n` is the numerator
of the rotated word `u ++ [b]`, which has the same `D`. -/
theorem word_step {b : Bool} {u : List Bool} {n : ℕ}
    (hlt : 3 ^ (b :: u).count true < 2 ^ (b :: u).length)
    (h : (2 ^ (b :: u).length - 3 ^ (b :: u).count true) * n = rhoW (b :: u)) :
    (2 ^ (b :: u).length - 3 ^ (b :: u).count true) * T n = rhoW (u ++ [b]) :=
  (word_step_aux hlt h).2

/-- Iterating `word_step`: `D(w) · T^[j] n = rhoW (w.rotate j)`. -/
theorem word_iterate (j : ℕ) {w : List Bool} {n : ℕ}
    (hlt : 3 ^ w.count true < 2 ^ w.length)
    (h : (2 ^ w.length - 3 ^ w.count true) * n = rhoW w) :
    (2 ^ w.length - 3 ^ w.count true) * T^[j] n = rhoW (w.rotate j) := by
  induction j generalizing w n with
  | zero => simpa using h
  | succ j ih =>
    cases w with
    | nil => simp at hlt
    | cons b u =>
      have h1 := word_step hlt h
      have hl := length_append_singleton' b u
      have hc := count_true_append_singleton b u
      rw [← hl, ← hc] at hlt h1 ⊢
      rw [Function.iterate_succ_apply, List.rotate_cons_succ]
      exact ih hlt h1

/-- If `D(w) · n = rhoW w` with `3^c < 2^L`, the first `j ≤ |w|` parities of the orbit of `n` are
the first `j` letters of `w`. -/
theorem parityWord_of_word (j : ℕ) {w : List Bool} {n : ℕ} (hj : j ≤ w.length)
    (hlt : 3 ^ w.count true < 2 ^ w.length)
    (h : (2 ^ w.length - 3 ^ w.count true) * n = rhoW w) :
    parityWord j n = w.take j := by
  induction j generalizing w n with
  | zero => simp [parityWord]
  | succ j ih =>
    cases w with
    | nil => simp at hj
    | cons b u =>
      have h0 := word_step_mod_two hlt h
      have h1 := word_step hlt h
      have hl := length_append_singleton' b u
      have hc := count_true_append_singleton b u
      rw [← hl, ← hc] at hlt h1
      have hj' : j ≤ u.length := by simp at hj; omega
      rw [parityWord, List.take_succ_cons, ih (by simp; omega) hlt h1,
        List.take_append_of_le_length hj']
      congr 1
      cases b <;> simp [h0]

/-- **Converse cycle equation.** If `3^c < 2^L` and `2^L − 3^c ∣ rhoW w`, then
`rhoW w / (2^L − 3^c)` is a `T`-periodic point with period dividing `L`. It need not have least
period `L`, and it may be `0`, e.g. for `w = [false]`. -/
theorem cycle_of_word {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length)
    (hd : (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w) :
    T^[w.length] (rhoW w / (2 ^ w.length - 3 ^ w.count true)) =
      rhoW w / (2 ^ w.length - 3 ^ w.count true) := by
  have hDpos : 0 < 2 ^ w.length - 3 ^ w.count true := by omega
  have hn := Nat.mul_div_cancel' hd
  generalize rhoW w / (2 ^ w.length - 3 ^ w.count true) = n at hn ⊢
  have := word_iterate w.length hlt hn
  rw [List.rotate_length, ← hn] at this
  exact Nat.eq_of_mul_eq_mul_left hDpos this

/-- The periodic point of `cycle_of_word` has parity word exactly `w`. -/
theorem parityWord_cycle_of_word {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length)
    (hd : (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w) :
    parityWord w.length (rhoW w / (2 ^ w.length - 3 ^ w.count true)) = w := by
  rw [parityWord_of_word w.length le_rfl hlt (Nat.mul_div_cancel' hd), List.take_length]

/-! ### Cycles as a divisibility statement on words -/

/-- Divisibility form of the absence of nontrivial cycles: for every parity word `w` with
`3^c < 2^L`, if `2^L − 3^c ∣ rhoW w` then the quotient is at most `2`. It mentions no dynamics:
it concerns `Σ 3^{c-1-i} 2^{e_i}` modulo `2^L − 3^c` over `0 ≤ e_0 < ⋯ < e_{c-1} < L`. -/
def CycleDivStatement : Prop :=
  ∀ w : List Bool, 3 ^ w.count true < 2 ^ w.length →
    (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w →
    rhoW w / (2 ^ w.length - 3 ^ w.count true) ≤ 2

/-- No positive `C`-cycle other than the trivial cycle `{1, 4, 2}`. -/
def NoNontrivialCycles : Prop :=
  ∀ n : ℕ, 0 < n → ∀ ℓ : ℕ, 0 < ℓ → C^[ℓ] n = n → n = 1 ∨ n = 2 ∨ n = 4

/-- A `T`-cycle of positive length through `n` is a `C`-cycle of positive length. -/
theorem C_cycle_of_T_cycle {n L : ℕ} (hL : 0 < L) (h : T^[L] n = n) :
    ∃ ℓ, 0 < ℓ ∧ C^[ℓ] n = n := by
  obtain ⟨e, he0, he⟩ := exists_iterate_C_eq_T n
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [Function.iterate_succ_apply] at h
  obtain ⟨i, hi⟩ := exists_iterate_T_eq_iterate_C L' (T n)
  refine ⟨i + e, by omega, ?_⟩
  rw [Function.iterate_add_apply, ← he, ← hi, h]

/-- The `T`-orbit of `1` stays in `{1, 2}`. -/
theorem iterate_T_one_mem' (j : ℕ) : T^[j] 1 = 1 ∨ T^[j] 1 = 2 := by
  induction j with
  | zero => left; rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h]
    · right; decide
    · left; decide

/-- `4` is not `T`-periodic: `T 4 = 2`, and the orbit of `2` is `{1, 2}`. -/
theorem not_T_cycle_four {L : ℕ} (hL : 0 < L) : T^[L] 4 ≠ 4 := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have e : T^[L' + 1] 4 = T^[L' + 1] 1 := by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      show T 4 = 2 by decide, show T 1 = 2 by decide]
  rw [e]
  rcases iterate_T_one_mem' (L' + 1) with h | h <;> omega

/-- `CycleDivStatement` implies the absence of nontrivial `C`-cycles, stated pointwise. -/
theorem noNontrivialCycles_of_cycleDiv (H : CycleDivStatement) (n : ℕ) (hn : 0 < n) (ℓ : ℕ)
    (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) : n = 1 ∨ n = 2 ∨ n = 4 := by
  refine goal_of_no_min_odd_T_cycle (fun m L h1 h2 hL hc _ => ?_) n hn ℓ hℓ h
  have hlt := three_pow_lt_two_pow_of_cycle (by omega) hL hc
  have he := cycle_eq_word hc
  have hlen := length_parityWord L m
  have hcnt := count_parityWord L m
  have H' := H (parityWord L m)
  rw [hlen, hcnt] at H'
  have hDpos : 0 < 2 ^ L - 3 ^ oddSteps L m := by omega
  have := H' hlt ⟨m, he.symm⟩
  rw [← he, Nat.mul_div_cancel_left m hDpos] at this
  omega

/-- The absence of nontrivial cycles implies `CycleDivStatement`, via `cycle_of_word`. -/
theorem cycleDiv_of_noNontrivialCycles (G : NoNontrivialCycles) : CycleDivStatement := by
  intro w hlt hd
  have hc := cycle_of_word hlt hd
  generalize rhoW w / (2 ^ w.length - 3 ^ w.count true) = n at hc ⊢
  have hL : 0 < w.length := by
    rcases Nat.eq_zero_or_pos w.length with h0 | h0
    · rw [h0] at hlt; simp at hlt
    · exact h0
  rcases Nat.eq_zero_or_pos n with h0 | h0
  · omega
  obtain ⟨ℓ, hℓ, hC⟩ := C_cycle_of_T_cycle hL hc
  rcases G n h0 ℓ hℓ hC with h1 | h1 | h1
  · omega
  · omega
  · exact absurd (h1 ▸ hc) (not_T_cycle_four hL)

/-- **No nontrivial cycles as a statement on words.** -/
theorem noNontrivialCycles_iff_cycleDiv : NoNontrivialCycles ↔ CycleDivStatement :=
  ⟨cycleDiv_of_noNontrivialCycles, fun H ↦ noNontrivialCycles_of_cycleDiv H⟩

/-! ### Bounds on the word numerator -/

/-- **Lower bound.** `3^c ≤ rhoW w + 2^c`, i.e. `rhoW w ≥ 3^c − 2^c`. -/
theorem rhoW_lower (w : List Bool) : 3 ^ w.count true ≤ rhoW w + 2 ^ w.count true := by
  induction w with
  | nil => simp [rhoW]
  | cons b u ih =>
    rw [rhoW, count_true_cons]
    cases b
    · simp only [Bool.false_eq_true, ite_false, add_zero]; omega
    · simp only [ite_true, pow_succ]; omega

/-- **Upper bound.** `rhoW w + 2^L ≤ 3^c · 2^{L−c}`, i.e. `rhoW w ≤ 2^{L−c} (3^c − 2^c)`. -/
theorem rhoW_upper (w : List Bool) :
    rhoW w + 2 ^ w.length ≤ 3 ^ w.count true * 2 ^ (w.length - w.count true) := by
  induction w with
  | nil => simp [rhoW]
  | cons b u ih =>
    have hcl : u.count true ≤ u.length := List.count_le_length
    have hP : 0 < 2 ^ (u.length - u.count true) := by positivity
    have hle : 3 ^ u.count true ≤ 3 ^ u.count true * 2 ^ (u.length - u.count true) :=
      Nat.le_mul_of_pos_right _ hP
    rw [rhoW, count_true_cons, List.length_cons]
    cases b
    · simp only [Bool.false_eq_true, ite_false, add_zero]
      rw [show u.length + 1 - u.count true = (u.length - u.count true) + 1 by omega,
        pow_succ, pow_succ]
      have : 3 ^ u.count true * (2 ^ (u.length - u.count true) * 2)
          = 2 * (3 ^ u.count true * 2 ^ (u.length - u.count true)) := by ring
      omega
    · simp only [ite_true]
      rw [show u.length + 1 - (u.count true + 1) = u.length - u.count true by omega,
        pow_succ, pow_succ]
      have : 3 ^ u.count true * 3 * 2 ^ (u.length - u.count true)
          = 3 * (3 ^ u.count true * 2 ^ (u.length - u.count true)) := by ring
      omega

/-- Every point `x` of a `T`-cycle satisfies `3^k ≤ (2^L − 3^k) · x + 2^k`, i.e. the
Böhm–Sontacchi lower bound `x ≥ (3^k − 2^k)/(2^L − 3^k)`. -/
theorem cycle_point_lower {x L : ℕ} (h : T^[L] x = x) :
    3 ^ oddSteps L x ≤ (2 ^ L - 3 ^ oddSteps L x) * x + 2 ^ oddSteps L x := by
  rw [cycle_eq_word h, ← count_parityWord L x]
  exact rhoW_lower _

/-- Every point `x` of a `T`-cycle satisfies `(2^L − 3^k) · x + 2^L ≤ 3^k · 2^{L−k}`, so the
points of a cycle with given `L` and `k` lie in an explicit finite range. -/
theorem cycle_point_upper {x L : ℕ} (h : T^[L] x = x) :
    (2 ^ L - 3 ^ oddSteps L x) * x + 2 ^ L ≤ 3 ^ oddSteps L x * 2 ^ (L - oddSteps L x) := by
  rw [cycle_eq_word h]
  have := rhoW_upper (parityWord L x)
  rwa [length_parityWord, count_parityWord] at this

/-! ### Examples -/

-- Small values of the word numerator.
example : rhoW [true, false] = 1 ∧ rhoW [false, true] = 2 := by decide

example : rhoW [true, true, false] = 5 := by decide

-- The converse recovers the trivial cycle `1 → 2 → 1` from the word `[true, false]`.
example : T^[2] 1 = 1 ∧ parityWord 2 1 = [true, false] := by
  have h1 := cycle_of_word (w := [true, false]) (by decide) (by decide)
  have h2 := parityWord_cycle_of_word (w := [true, false]) (by decide) (by decide)
  have e : rhoW [true, false] / (2 ^ [true, false].length - 3 ^ [true, false].count true) = 1 := by
    decide
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

-- The hypotheses of `CycleDivStatement` are satisfiable: `[true, false]` gives quotient `1` and
-- `[false, true]` gives quotient `2`.
example : 3 ^ [true, false].count true < 2 ^ [true, false].length ∧
    (2 ^ [true, false].length - 3 ^ [true, false].count true) ∣ rhoW [true, false] ∧
    rhoW [false, true] / (2 ^ [false, true].length - 3 ^ [false, true].count true) = 2 := by
  decide

-- The cycle-point bounds at the trivial cycle `x = 1`, `L = 2`, `k = 1`.
example : 3 ^ oddSteps 2 1 ≤ (2 ^ 2 - 3 ^ oddSteps 2 1) * 1 + 2 ^ oddSteps 2 1 ∧
    (2 ^ 2 - 3 ^ oddSteps 2 1) * 1 + 2 ^ 2 ≤ 3 ^ oddSteps 2 1 * 2 ^ (2 - oddSteps 2 1) :=
  ⟨cycle_point_lower (by decide), cycle_point_upper (by decide)⟩

end Collatz
