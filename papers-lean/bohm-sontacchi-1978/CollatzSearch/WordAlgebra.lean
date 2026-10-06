import CollatzSearch.CycleWord
import Mathlib.Data.List.Rotate
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-!
# Word algebra for `CycleDivStatement` (classical Böhm–Sontacchi algebra)

Notation: `L = |w|`, `c = #true w`, `D(w) = 2^L − 3^c` (ℕ subtraction, used under `3^c < 2^L`).

## Main results
* T1 `rhoW_append`: `rhoW (u ++ v) = 3^{#v}·rhoW u + 2^{|u|}·rhoW v`; closed forms
  `rhoW_replicate_true` (`rhoW 1^k + 2^k = 3^k`), `rhoW_replicate_false`, `rhoW_one_run`
  (`rhoW (1^k 0^l) + 2^k = 3^k`).
* T2 `D_odd`, `coprime_two_D`, `coprime_three_D`, `dvd_rhoW_rotate_iff`: `D(w) ∣ rhoW w` is
  invariant under rotation, proved arithmetically (no dynamics); `rhoW_rotate_div`: the quotient
  of the `j`-th rotation is `T^[j]` of the quotient.
* T3 `wpow`, `rhoW_wpow_int` (`R_r·(2^L−3^c) = ρ·(2^{rL}−3^{rc})` over ℤ), `dvd_rhoW_wpow_iff`,
  `rhoW_wpow_div`: a power `w^r` (`r ≥ 1`) satisfies the divisibility iff `w` does, with the same
  quotient; so `CycleDivStatement` need only be checked on primitive words up to rotation.
  `cycle_of_word_pos`: if moreover `c ≥ 1`, the cycle point is positive.

Honesty: all classical (Böhm–Sontacchi 1978 word algebra). This is bookkeeping that makes
`CycleDivStatement` easier to work with; it is **not** progress on the Goal, which remains open.
-/

namespace CollatzSearch
open CollatzProof

/-- **Concatenation law.** `rhoW (u ++ v) = 3^{#true v}·rhoW u + 2^{|u|}·rhoW v`. -/
theorem rhoW_append (u v : List Bool) :
    rhoW (u ++ v) = 3 ^ v.count true * rhoW u + 2 ^ u.length * rhoW v := by
  induction u with
  | nil => simp [rhoW]
  | cons b u ih =>
    rw [List.cons_append, rhoW, rhoW, ih, List.count_append, List.length_cons]
    cases b <;> simp [pow_add, pow_succ] <;> ring

/-- A run of `k` odd steps: `rhoW (1^k) + 2^k = 3^k`, i.e. `rhoW (1^k) = 3^k − 2^k`. -/
theorem rhoW_replicate_true (k : ℕ) : rhoW (List.replicate k true) + 2 ^ k = 3 ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [List.replicate_succ, rhoW, List.count_replicate_self, pow_succ, pow_succ]
    simp only [ite_true]; omega

/-- A run of even steps has numerator `0`. -/
theorem rhoW_replicate_false (l : ℕ) : rhoW (List.replicate l false) = 0 := by
  induction l with
  | zero => rfl
  | succ l ih => rw [List.replicate_succ, rhoW, ih]; simp

/-- One-run word: `rhoW (1^k 0^l) + 2^k = 3^k` (the zeros contribute nothing). -/
theorem rhoW_one_run (k l : ℕ) :
    rhoW (List.replicate k true ++ List.replicate l false) + 2 ^ k = 3 ^ k := by
  rw [rhoW_append, rhoW_replicate_false, List.count_replicate]
  simpa using rhoW_replicate_true k

example : rhoW ([true, true] ++ [false]) = 5 := by decide

/-- Rotating a leading `true` to the end: `2·rhoW (u++[1]) = 3·rhoW (1::u) + D`. -/
theorem two_mul_rhoW_rotate_true (u : List Bool)
    (hlt : 3 ^ (true :: u).count true < 2 ^ (true :: u).length) :
    2 * rhoW (u ++ [true]) = 3 * rhoW (true :: u) +
      (2 ^ (true :: u).length - 3 ^ (true :: u).count true) := by
  rw [rhoW_append_true, rhoW] at *
  simp only [List.count_cons_self, List.length_cons, ite_true, pow_succ] at *
  omega

/-- Rotating a leading `false` to the end: `2·rhoW (u++[0]) = rhoW (0::u)`. -/
theorem two_mul_rhoW_rotate_false (u : List Bool) :
    2 * rhoW (u ++ [false]) = rhoW (false :: u) := by
  rw [rhoW_append_false, rhoW]; simp

/-- `3^c < 2^L` forces `L ≥ 1`. -/
theorem length_pos_of_lt {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length) :
    0 < w.length := by
  rcases Nat.eq_zero_or_pos w.length with h | h
  · rw [h, List.length_eq_zero_iff.mp h] at hlt; simp at hlt
  · exact h

/-- `D(w) = 2^L − 3^c` is odd when `3^c < 2^L`. -/
theorem D_odd {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length) :
    (2 ^ w.length - 3 ^ w.count true) % 2 = 1 := by
  have hL := length_pos_of_lt hlt
  have h2 : 2 ^ w.length % 2 = 0 := by
    obtain ⟨m, hm⟩ : ∃ m, w.length = m + 1 := ⟨_, (Nat.succ_pred_eq_of_pos hL).symm⟩
    rw [hm, pow_succ]; simp
  have h3 := three_pow_mod_two (w.count true)
  omega

/-- `D(w)` is coprime to `2`. -/
theorem coprime_two_D {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length) :
    Nat.Coprime 2 (2 ^ w.length - 3 ^ w.count true) := by
  rw [Nat.coprime_two_left]
  exact Nat.odd_iff.mpr (D_odd hlt)

/-- `D(w)` is coprime to `3` when `c ≥ 1`. -/
theorem coprime_three_D {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length)
    (hc : 0 < w.count true) : Nat.Coprime 3 (2 ^ w.length - 3 ^ w.count true) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h
  have h3 : 3 ∣ 3 ^ w.count true := dvd_pow_self 3 hc.ne'
  have : 3 ∣ 2 ^ w.length := by
    have := Nat.dvd_add h h3
    rwa [Nat.sub_add_cancel hlt.le] at this
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

/-- `D(w) ∣ rhoW w ↔ D(w) ∣ rhoW (rotate w 1)` (arithmetic proof, no dynamics). -/
theorem dvd_rhoW_rotate_one_iff {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length) :
    (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w ↔
      (2 ^ w.length - 3 ^ w.count true) ∣ rhoW (w.rotate 1) := by
  cases w with
  | nil => simp
  | cons b u =>
    have h2 := coprime_two_D hlt
    rw [List.rotate_cons_succ, List.rotate_zero]
    cases b with
    | false =>
      have e := two_mul_rhoW_rotate_false u
      constructor
      · intro h; rw [← e] at h; exact h2.symm.dvd_of_dvd_mul_left h
      · intro h; rw [← e]; exact Dvd.dvd.mul_left h 2
    | true =>
      have e := two_mul_rhoW_rotate_true u hlt
      have h3 := coprime_three_D hlt (by simp)
      constructor
      · intro h
        have : (2 ^ (true :: u).length - 3 ^ (true :: u).count true) ∣ 2 * rhoW (u ++ [true]) := by
          rw [e]; exact Nat.dvd_add (Dvd.dvd.mul_left h 3) dvd_rfl
        exact h2.symm.dvd_of_dvd_mul_left this
      · intro h
        have h' := Dvd.dvd.mul_left h 2
        rw [e] at h'
        exact h3.symm.dvd_of_dvd_mul_left ((Nat.dvd_add_left (dvd_refl _)).mp h')

/-- **Rotation invariance.** `D(w) ∣ rhoW w ↔ D(w) ∣ rhoW (rotate w j)` for every `j`. -/
theorem dvd_rhoW_rotate_iff {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length) (j : ℕ) :
    (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w ↔
      (2 ^ w.length - 3 ^ w.count true) ∣ rhoW (w.rotate j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have hl : (w.rotate j).length = w.length := List.length_rotate w j
    have hc : (w.rotate j).count true = w.count true := (List.rotate_perm w j).count_eq true
    have hlt' : 3 ^ (w.rotate j).count true < 2 ^ (w.rotate j).length := by rwa [hl, hc]
    have := dvd_rhoW_rotate_one_iff hlt'
    rw [hl, hc, List.rotate_rotate] at this
    rw [ih, this]

/-- **Quotient identity.** If `D(w) ∣ rhoW w`, then
`rhoW (rotate w j) / D(w) = T^[j] (rhoW w / D(w))`. -/
theorem rhoW_rotate_div {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length)
    (hd : (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w) (j : ℕ) :
    rhoW (w.rotate j) / (2 ^ w.length - 3 ^ w.count true) =
      T^[j] (rhoW w / (2 ^ w.length - 3 ^ w.count true)) := by
  have hDpos : 0 < 2 ^ w.length - 3 ^ w.count true := by omega
  have hn := Nat.mul_div_cancel' hd
  rw [← word_iterate j hlt hn, Nat.mul_div_cancel_left _ hDpos]

/-- `wpow w r = w ++ w ++ ⋯ ++ w` (`r` copies). -/
def wpow (w : List Bool) : ℕ → List Bool
  | 0 => []
  | r + 1 => w ++ wpow w r

/-- `|w^r| = r·|w|`. -/
theorem length_wpow (w : List Bool) (r : ℕ) : (wpow w r).length = r * w.length := by
  induction r with
  | zero => simp [wpow]
  | succ r ih => rw [wpow, List.length_append, ih]; ring

/-- `#true (w^r) = r·#true w`. -/
theorem count_wpow (w : List Bool) (r : ℕ) : (wpow w r).count true = r * w.count true := by
  induction r with
  | zero => simp [wpow]
  | succ r ih => rw [wpow, List.count_append, ih]; ring

/-- **Power law over ℤ.** `rhoW(w^r)·(2^L − 3^c) = rhoW(w)·(2^{rL} − 3^{rc})`. -/
theorem rhoW_wpow_int (w : List Bool) (r : ℕ) :
    (rhoW (wpow w r) : ℤ) * (2 ^ w.length - 3 ^ w.count true) =
      (rhoW w : ℤ) * (2 ^ (r * w.length) - 3 ^ (r * w.count true)) := by
  induction r with
  | zero => simp [wpow, rhoW]
  | succ r ih =>
    have e : rhoW (wpow w (r + 1)) = 3 ^ (r * w.count true) * rhoW w + 2 ^ w.length * rhoW (wpow w r) := by
      rw [wpow, rhoW_append, count_wpow]
    rw [e, add_mul, add_mul, one_mul, one_mul, pow_add, pow_add]
    push_cast
    linear_combination (2 : ℤ) ^ w.length * ih

/-- `3^c < 2^L` and `r ≥ 1` give `3^{#(w^r)} < 2^{|w^r|}`. -/
theorem D_wpow_pos {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length) {r : ℕ} (hr : 0 < r) :
    3 ^ (wpow w r).count true < 2 ^ (wpow w r).length := by
  rw [length_wpow, count_wpow, mul_comm r, mul_comm r, pow_mul, pow_mul]
  exact Nat.pow_lt_pow_left hlt hr.ne'

/-- ℕ form of the power law: `rhoW(w^r)·D(w) = rhoW(w)·D(w^r)` (for `3^c<2^L`, `r ≥ 1`). -/
theorem rhoW_wpow_nat {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length) {r : ℕ} (hr : 0 < r) :
    rhoW (wpow w r) * (2 ^ w.length - 3 ^ w.count true) =
      rhoW w * (2 ^ (wpow w r).length - 3 ^ (wpow w r).count true) := by
  have h2 := D_wpow_pos hlt hr
  rw [length_wpow, count_wpow] at h2 ⊢
  have := rhoW_wpow_int w r
  zify [hlt.le, h2.le]
  exact this

/-- **Power reduction.** For `r ≥ 1`: `D(w^r) ∣ rhoW(w^r) ↔ D(w) ∣ rhoW w`. -/
theorem dvd_rhoW_wpow_iff {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length) {r : ℕ}
    (hr : 0 < r) :
    (2 ^ (wpow w r).length - 3 ^ (wpow w r).count true) ∣ rhoW (wpow w r) ↔
      (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w := by
  have e := rhoW_wpow_nat hlt hr
  have hD : 0 < 2 ^ w.length - 3 ^ w.count true := by omega
  have hDr : 0 < 2 ^ (wpow w r).length - 3 ^ (wpow w r).count true := by
    have := D_wpow_pos hlt hr; omega
  generalize 2 ^ w.length - 3 ^ w.count true = D at *
  generalize 2 ^ (wpow w r).length - 3 ^ (wpow w r).count true = Dr at *
  constructor
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn] at e
    apply Nat.eq_of_mul_eq_mul_left hDr
    rw [mul_comm Dr (rhoW w), ← e]; ring
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    rw [hn] at e
    apply Nat.eq_of_mul_eq_mul_left hD
    rw [mul_comm D (rhoW _), e]; ring

/-- **Power reduction, quotients.** For `r ≥ 1` and `D(w) ∣ rhoW w`, the cycle point of `w^r`
equals that of `w`. -/
theorem rhoW_wpow_div {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length) {r : ℕ}
    (hr : 0 < r) (hd : (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w) :
    rhoW (wpow w r) / (2 ^ (wpow w r).length - 3 ^ (wpow w r).count true) =
      rhoW w / (2 ^ w.length - 3 ^ w.count true) := by
  have e := rhoW_wpow_nat hlt hr
  have hD : 0 < 2 ^ w.length - 3 ^ w.count true := by omega
  have hDr : 0 < 2 ^ (wpow w r).length - 3 ^ (wpow w r).count true := by
    have := D_wpow_pos hlt hr; omega
  generalize 2 ^ w.length - 3 ^ w.count true = D at *
  generalize 2 ^ (wpow w r).length - 3 ^ (wpow w r).count true = Dr at *
  obtain ⟨n, hn⟩ := hd
  rw [hn] at e ⊢
  have : rhoW (wpow w r) = Dr * n := by
    apply Nat.eq_of_mul_eq_mul_left hD
    rw [mul_comm D (rhoW _), e]; ring
  rw [this, Nat.mul_div_cancel_left _ hDr, Nat.mul_div_cancel_left _ hD]

/-- **Positive cycle point.** If `3^c < 2^L`, `D(w) ∣ rhoW w` and `c ≥ 1`, then
`rhoW w / D(w) > 0`. -/
theorem cycle_of_word_pos {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length)
    (hd : (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w) (hc : 0 < w.count true) :
    0 < rhoW w / (2 ^ w.length - 3 ^ w.count true) := by
  have hD : 0 < 2 ^ w.length - 3 ^ w.count true := by omega
  have hl := rhoW_lower w
  have h23 : 2 ^ w.count true < 3 ^ w.count true :=
    Nat.pow_lt_pow_left (by norm_num) hc.ne'
  have hpos : 0 < rhoW w := by omega
  exact Nat.div_pos (Nat.le_of_dvd hpos hd) hD

/-- Convenience: `cycle_of_word` together with positivity of the cycle point. -/
theorem cycle_of_word_pos' {w : List Bool} (hlt : 3 ^ w.count true < 2 ^ w.length)
    (hd : (2 ^ w.length - 3 ^ w.count true) ∣ rhoW w) (hc : 0 < w.count true) :
    T^[w.length] (rhoW w / (2 ^ w.length - 3 ^ w.count true)) =
        rhoW w / (2 ^ w.length - 3 ^ w.count true) ∧
      0 < rhoW w / (2 ^ w.length - 3 ^ w.count true) :=
  ⟨(cycle_of_word hlt hd).1, cycle_of_word_pos hlt hd hc⟩

example : rhoW (wpow [true, false] 2) = 7 ∧ rhoW (wpow [true, false, false] 2) = 11 := by decide

example : rhoW [true, false, false] = 1 ∧ rhoW ([true, false, false].rotate 1) = 4 ∧
    2 * 4 = 3 * 1 + (2 ^ 3 - 3 ^ 1) := by decide

end CollatzSearch

#print axioms CollatzSearch.rhoW_append
#print axioms CollatzSearch.rhoW_replicate_true
#print axioms CollatzSearch.rhoW_replicate_false
#print axioms CollatzSearch.rhoW_one_run
#print axioms CollatzSearch.two_mul_rhoW_rotate_true
#print axioms CollatzSearch.two_mul_rhoW_rotate_false
#print axioms CollatzSearch.length_pos_of_lt
#print axioms CollatzSearch.D_odd
#print axioms CollatzSearch.coprime_two_D
#print axioms CollatzSearch.coprime_three_D
#print axioms CollatzSearch.dvd_rhoW_rotate_one_iff
#print axioms CollatzSearch.dvd_rhoW_rotate_iff
#print axioms CollatzSearch.rhoW_rotate_div
#print axioms CollatzSearch.length_wpow
#print axioms CollatzSearch.count_wpow
#print axioms CollatzSearch.rhoW_wpow_int
#print axioms CollatzSearch.D_wpow_pos
#print axioms CollatzSearch.rhoW_wpow_nat
#print axioms CollatzSearch.dvd_rhoW_wpow_iff
#print axioms CollatzSearch.rhoW_wpow_div
#print axioms CollatzSearch.cycle_of_word_pos
#print axioms CollatzSearch.cycle_of_word_pos'
