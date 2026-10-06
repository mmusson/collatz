import Collatz.Affine
import Mathlib.Data.List.Rotate

/-!
# Parity words and the Böhm–Sontacchi correspondence (exact IFF)

For a parity word `w : List Bool` (`true` = odd step) with `L = |w|`, `c = #true(w)`, the
*word numerator* is `rhoW w = Σ_i 3^{c-1-i} 2^{e_i}` where `e_0 < … < e_{c-1}` are the positions
of `true` (defined by head recursion `rhoW (b :: u) = 2·rhoW u + [b]·3^{#true u}`), and
`D(w) = 2^L − 3^c`.

## Main results
* T1 (`rho_eq_rhoW`, `count_parityWord`, `length_parityWord`): the Terras remainder `rho j n`
  is the numerator of the parity word of `n`.
* T1 (`cycle_eq_word`): forward Böhm–Sontacchi: a `T`-cycle `T^L m = m` has
  `(2^L − 3^k)·m = rhoW (parityWord L m)`.
* T1 (`cycle_of_word`): **converse**: if `3^c < 2^L` and `D(w) ∣ rhoW w`, then
  `n = rhoW w / D(w)` satisfies `T^[L] n = n` (not necessarily minimal period; `n` may be `0`,
  e.g. `w = [false]`) and has parity word exactly `w`.
* T2 (`goal_iff_cycleDiv`): the no-nontrivial-cycles statement (`GoalStatement`) is
  equivalent
  to `CycleDivStatement`, a statement mentioning no dynamics: for all words with `3^c < 2^L`,
  `D(w) ∣ rhoW w → rhoW w / D(w) ≤ 2`. `goal_of_cycleDiv` is the usable half, stated for `C`-cycles.
* T3 (`rhoW_lower`, `rhoW_upper`, `cycle_point_lower`, `cycle_point_upper`): `3^c − 2^c ≤ rhoW w`
  and `rhoW w + 2^L ≤ 3^c·2^{L−c}`; hence each cycle point `x` satisfies
  `3^k ≤ (2^L−3^k)·x + 2^k` (Böhm–Sontacchi minimum bound) and
  `(2^L−3^k)·x + 2^L ≤ 3^k·2^{L−k}`.

All of this is classical (Böhm–Sontacchi 1978).
-/

namespace Collatz
open CollatzProof

/-- Word numerator: `rhoW [] = 0`, `rhoW (b :: u) = 2·rhoW u + [b]·3^{#true u}`; equivalently
`Σ_i 3^{c-1-i} 2^{e_i}` over the positions `e_0 < … < e_{c-1}` of `true`. -/
def rhoW : List Bool → ℕ
  | [] => 0
  | b :: w => 2 * rhoW w + (if b then 3 ^ w.count true else 0)

/-- `parityWord j n = [n odd, T n odd, …, T^{j-1} n odd]`. -/
def parityWord : ℕ → ℕ → List Bool
  | 0, _ => []
  | j + 1, n => decide (n % 2 = 1) :: parityWord j (T n)

example : rhoW [true, false] = 1 ∧ rhoW [false, true] = 2 := by decide

/-- `#true (b :: u) = #true u + [b]`. -/
theorem count_true_cons (b : Bool) (u : List Bool) :
    (b :: u).count true = u.count true + (if b then 1 else 0) := by
  cases b <;> simp

/-- Rotating one letter preserves the number of `true`s. -/
theorem count_true_append_singleton (b : Bool) (u : List Bool) :
    (u ++ [b]).count true = (b :: u).count true := by
  cases b <;> simp [List.count_append]

/-- Rotating one letter preserves length. -/
theorem length_append_singleton' (b : Bool) (u : List Bool) :
    (u ++ [b]).length = (b :: u).length := by simp

/-- The parity word of length `j` has length `j`. -/
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

/-- Appending an odd step: `rhoW (w ++ [true]) = 3·rhoW w + 2^{|w|}`. -/
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

/-- One step of the converse: if `D(w)·n = rhoW w` for `w = b :: u` with `3^c < 2^L`, then the
parity of `n` is `b` and `D(w)·T n = rhoW (u ++ [b])` (the rotated word; same `D`). -/
theorem word_step {b : Bool} {u : List Bool} {n : ℕ}
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

/-- Iterating `word_step`: `D(w)·T^j n = rhoW (rotate w j)`. -/
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
      obtain ⟨-, h1⟩ := word_step hlt h
      have hl := length_append_singleton' b u
      have hc := count_true_append_singleton b u
      rw [← hl, ← hc] at hlt h1 ⊢
      rw [Function.iterate_succ_apply, List.rotate_cons_succ]
      exact ih hlt h1

/-- If `D(w)·n = rhoW w` (with `3^c < 2^L`), the first `j ≤ |w|` parities of the orbit of `n`
are the first `j` letters of `w`. -/
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
      obtain ⟨h0, h1⟩ := word_step hlt h
      have hl := length_append_singleton' b u
      have hc := count_true_append_singleton b u
      rw [← hl, ← hc] at hlt h1
      have hj' : j ≤ u.length := by simp at hj; omega
      rw [parityWord, List.take_succ_cons, ih (by simp; omega) hlt h1,
        List.take_append_of_le_length hj']
      congr 1
      cases b <;> simp [h0]

/-- **Forward Böhm–Sontacchi.** A `T`-cycle `T^L m = m` satisfies
`(2^L − 3^k)·m = rhoW (parityWord L m)`, `k = oddSteps L m`. -/
theorem cycle_eq_word {m L : ℕ} (h : T^[L] m = m) :
    (2 ^ L - 3 ^ oddSteps L m) * m = rhoW (parityWord L m) := by
  rw [← rho_eq_rhoW, Nat.sub_mul]
  have := cycle_equation h
  omega

/-- **Converse Böhm–Sontacchi.** If `3^c < 2^L` and `2^L − 3^c ∣ rhoW w`, then
`n = rhoW w / (2^L − 3^c)` satisfies `T^[L] n = n` (not necessarily minimal period; `n` may be
`0`, e.g. `w = [false]`) and its parity word of length `L` is `w`. -/
theorem cycle_of_word {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length)
    (hd : (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w) :
    let n := rhoW w / (2 ^ w.length - 3 ^ w.count true)
    T^[w.length] n = n ∧ parityWord w.length n = w := by
  intro n
  have hDpos : 0 < 2 ^ w.length - 3 ^ w.count true := by omega
  have hn : (2 ^ w.length - 3 ^ w.count true) * n = rhoW w := Nat.mul_div_cancel' hd
  refine ⟨?_, ?_⟩
  · have := word_iterate w.length hlt hn
    rw [List.rotate_length, ← hn] at this
    exact Nat.eq_of_mul_eq_mul_left hDpos this
  · rw [parityWord_of_word w.length le_rfl hlt hn, List.take_length]

example : T^[2] 1 = 1 ∧ parityWord 2 1 = [true, false] := by
  obtain ⟨h1, h2⟩ := cycle_of_word (w := [true, false]) (by decide) (by decide)
  have e : rhoW [true, false] / (2 ^ [true, false].length - 3 ^ [true, false].count true) = 1 := by
    decide
  rw [e] at h1 h2
  exact ⟨h1, h2⟩

/-! ### T2: the no-nontrivial-cycles statement as a pure divisibility statement on words -/

/-- Pure divisibility form of the no-nontrivial-cycles statement: for every parity word `w` with `3^c < 2^L`, if
`2^L − 3^c ∣ rhoW w` then the quotient is `≤ 2`. It mentions no dynamics: it is a statement about
`Σ 3^{c-1-i} 2^{e_i}` modulo `2^L − 3^c` over `0 ≤ e_0 < … < e_{c-1} < L`, and is the natural
target for arithmetic attacks (mod-p on Farey cones, 2-adic). -/
def CycleDivStatement : Prop :=
  ∀ w : List Bool, 3 ^ w.count true < 2 ^ w.length →
    (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w →
    rhoW w / (2 ^ w.length - 3 ^ w.count true) ≤ 2

/-- The statement of `no_nontrivial_cycles`, as a `Prop`. -/
def GoalStatement : Prop :=
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

/-- Local copy of `Sanity.iterate_T_one_mem` (to keep imports narrow). -/
theorem iterate_T_one_mem' (j : ℕ) : T^[j] 1 = 1 ∨ T^[j] 1 = 2 := by
  induction j with
  | zero => left; rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h]
    · right; decide
    · left; decide

/-- `4` is not `T`-periodic (`T 4 = 2`, and the orbit of `2` is `{1,2}`). -/
theorem not_T_cycle_four {L : ℕ} (hL : 0 < L) : T^[L] 4 ≠ 4 := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have e : T^[L' + 1] 4 = T^[L' + 1] 1 := by
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      show T 4 = 2 by decide, show T 1 = 2 by decide]
  rw [e]
  rcases iterate_T_one_mem' (L' + 1) with h | h <;> omega

/-- `CycleDivStatement` implies `GoalStatement`, stated in the exact shape of `no_nontrivial_cycles`. -/
theorem goal_of_cycleDiv (H : CycleDivStatement) (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) : n = 1 ∨ n = 2 ∨ n = 4 := by
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

/-- `GoalStatement` implies `CycleDivStatement` (uses the converse `cycle_of_word`). -/
theorem cycleDiv_of_goal (G : GoalStatement) : CycleDivStatement := by
  intro w hlt hd
  obtain ⟨hc, -⟩ := cycle_of_word hlt hd
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

/-- **`GoalStatement` ⇔ `CycleDivStatement`.** -/
theorem goal_iff_cycleDiv : GoalStatement ↔ CycleDivStatement :=
  ⟨cycleDiv_of_goal, fun H => goal_of_cycleDiv H⟩

/-! ### T3: word-level numerator bounds -/

/-- `#true w ≤ |w|`. -/
theorem count_le_length' (w : List Bool) : w.count true ≤ w.length := List.count_le_length

/-- **Lower bound.** `3^c ≤ rhoW w + 2^c`, i.e. `rhoW w ≥ 3^c − 2^c`. -/
theorem rhoW_lower (w : List Bool) : 3 ^ w.count true ≤ rhoW w + 2 ^ w.count true := by
  induction w with
  | nil => simp [rhoW]
  | cons b u ih =>
    rw [rhoW, count_true_cons]
    cases b
    · simp only [Bool.false_eq_true, ite_false, add_zero]; omega
    · simp only [ite_true, pow_succ]; omega

/-- **Upper bound.** `rhoW w + 2^L ≤ 3^c·2^{L−c}`, i.e. `rhoW w ≤ 2^{L−c}(3^c − 2^c)`. -/
theorem rhoW_upper (w : List Bool) :
    rhoW w + 2 ^ w.length ≤ 3 ^ w.count true * 2 ^ (w.length - w.count true) := by
  induction w with
  | nil => simp [rhoW]
  | cons b u ih =>
    have hcl := count_le_length' u
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

/-- Every point `x` of a `T`-cycle satisfies `3^k ≤ (2^L − 3^k)·x + 2^k` (Böhm–Sontacchi
lower bound `x ≥ (3^k − 2^k)/(2^L − 3^k)`). No positivity hypothesis needed. -/
theorem cycle_point_lower {x L : ℕ} (h : T^[L] x = x) :
    3 ^ oddSteps L x ≤ (2 ^ L - 3 ^ oddSteps L x) * x + 2 ^ oddSteps L x := by
  rw [cycle_eq_word h, ← count_parityWord L x]
  exact rhoW_lower _

/-- Every point `x` of a `T`-cycle satisfies `(2^L − 3^k)·x + 2^L ≤ 3^k·2^{L−k}`
(word-level form of `RhoBound.cycle_finite_range`). -/
theorem cycle_point_upper {x L : ℕ} (h : T^[L] x = x) :
    (2 ^ L - 3 ^ oddSteps L x) * x + 2 ^ L ≤ 3 ^ oddSteps L x * 2 ^ (L - oddSteps L x) := by
  rw [cycle_eq_word h]
  have := rhoW_upper (parityWord L x)
  rwa [length_parityWord, count_parityWord] at this

example : rhoW [true, true, false] = 5 := by decide

/-- Non-vacuity of `CycleDivStatement`'s hypotheses: `w = [true, false]` has `3 < 4`,
`D = 1 ∣ rhoW w = 1`, quotient `1` (the trivial cycle); `w = [false, true]` gives quotient `2`. -/
example : 3 ^ [true, false].count true < 2 ^ [true, false].length ∧
    (2 ^ [true, false].length - 3 ^ [true, false].count true) ∣ rhoW [true, false] ∧
    rhoW [false, true] / (2 ^ [false, true].length - 3 ^ [false, true].count true) = 2 := by
  decide

/-- Bounds at the trivial cycle `x = 1`, `L = 2`, `k = 1`: `3 ≤ 1 + 2` and `1 + 4 ≤ 6`. -/
example : 3 ^ oddSteps 2 1 ≤ (2 ^ 2 - 3 ^ oddSteps 2 1) * 1 + 2 ^ oddSteps 2 1 ∧
    (2 ^ 2 - 3 ^ oddSteps 2 1) * 1 + 2 ^ 2 ≤ 3 ^ oddSteps 2 1 * 2 ^ (2 - oddSteps 2 1) :=
  ⟨cycle_point_lower (by decide), cycle_point_upper (by decide)⟩

end Collatz

#print axioms Collatz.count_true_cons
#print axioms Collatz.count_true_append_singleton
#print axioms Collatz.length_append_singleton'
#print axioms Collatz.length_parityWord
#print axioms Collatz.count_parityWord
#print axioms Collatz.rho_eq_rhoW
#print axioms Collatz.rhoW_append_true
#print axioms Collatz.rhoW_append_false
#print axioms Collatz.word_step
#print axioms Collatz.word_iterate
#print axioms Collatz.parityWord_of_word
#print axioms Collatz.cycle_eq_word
#print axioms Collatz.cycle_of_word
#print axioms Collatz.C_cycle_of_T_cycle
#print axioms Collatz.iterate_T_one_mem'
#print axioms Collatz.not_T_cycle_four
#print axioms Collatz.goal_of_cycleDiv
#print axioms Collatz.cycleDiv_of_goal
#print axioms Collatz.goal_iff_cycleDiv
#print axioms Collatz.count_le_length'
#print axioms Collatz.rhoW_lower
#print axioms Collatz.rhoW_upper
#print axioms Collatz.cycle_point_lower
#print axioms Collatz.cycle_point_upper
