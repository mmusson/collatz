import CollatzSearch.CycleInvariance
import CollatzSearch.Diophantine
import CollatzSearch.RhoBound

/-!
# Hygiene repairs

* `nontrivial_C_cycle_L_ge`: named corollary giving the cycle-length bound `971 ≤ L` directly.
* Non-vacuity examples: the trivial `T`-cycle `1 → 2 → 1` (`m = 1`, `L = 2`, `k = S_2(1) = 1`)
  satisfies the hypotheses of `cycle_diophantine`, `cycle_L_determined` (whose extra hypothesis
  `2k ≤ 3m` reads `2 ≤ 3`) and `cycle_finite_range`.

Note: `cycle_L_determined` is **conditional** on `2k ≤ 3m`; nothing in the library discharges
that hypothesis for a hypothetical nontrivial cycle.
-/

namespace CollatzSearch
open CollatzProof

/-- A nontrivial positive `C`-cycle through `n` yields an odd `m` with `2^17 ≤ m ≤ n` on a
`T`-cycle of length `L` with `971 ≤ L`. (Classical Crandall/Eliahou-type bound, small range.) -/
theorem nontrivial_C_cycle_L_ge (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∃ m L, m % 2 = 1 ∧ 2 ^ 17 ≤ m ∧ m ≤ n ∧ 0 < L ∧
      T^[L] m = m ∧ 971 ≤ L := by
  obtain ⟨m, L, h1, h2, h3, h4, h5, -, h7, h8, -⟩ := nontrivial_C_cycle_bounds' n hn ℓ hℓ h hne
  exact ⟨m, L, h1, h2, h3, h4, h5, le_trans h7 h8⟩

/-- The trivial `T`-cycle: `T^2 1 = 1`. -/
theorem T_two_one : T^[2] 1 = 1 := by decide

/-- Every point of the orbit of `1` is `1` or `2`. -/
theorem iterate_T_one_mem (j : ℕ) : T^[j] 1 = 1 ∨ T^[j] 1 = 2 := by
  induction j with
  | zero => left; rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h <;> rw [h]
    · right; decide
    · left; decide

/-- `1` is the minimum of its `T`-orbit. -/
theorem one_le_iterate_T_one (j : ℕ) : 1 ≤ T^[j] 1 := by
  rcases iterate_T_one_mem j with h | h <;> omega

theorem oddSteps_two_one : oddSteps 2 1 = 1 := by decide

/-- Non-vacuity of `cycle_diophantine` at the trivial cycle. -/
example : 2 ^ 2 * (3 * 1) ≤ 3 ^ (oddSteps 2 1) * (3 * 1) + oddSteps 2 1 * 2 ^ 2 :=
  cycle_diophantine (m := 1) (L := 2) (by norm_num) T_two_one one_le_iterate_T_one

/-- Non-vacuity of `cycle_L_determined` at the trivial cycle (`2k ≤ 3m` is `2 ≤ 3`). -/
example : 2 ^ (2 - 1) < 3 ^ (oddSteps 2 1) ∧ 3 ^ (oddSteps 2 1) < 2 ^ 2 :=
  cycle_L_determined (m := 1) (L := 2) (by norm_num) T_two_one one_le_iterate_T_one
    (by rw [oddSteps_two_one]; norm_num) (by norm_num)

/-- Non-vacuity of `cycle_finite_range` at the trivial cycle. -/
example : 1 * 2 ^ 2 * 2 ^ (oddSteps 2 1) + 2 ^ 2 * 2 ^ (oddSteps 2 1) ≤
    1 * 3 ^ (oddSteps 2 1) * 2 ^ (oddSteps 2 1) + 2 ^ 2 * 3 ^ (oddSteps 2 1) :=
  cycle_finite_range (m := 1) (L := 2) T_two_one

end CollatzSearch

#print axioms CollatzSearch.nontrivial_C_cycle_L_ge
#print axioms CollatzSearch.iterate_T_one_mem
#print axioms CollatzSearch.one_le_iterate_T_one
#print axioms CollatzSearch.oddSteps_two_one
#print axioms CollatzSearch.T_two_one
