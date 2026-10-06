import CollatzSearch.OddStepBound

/-!
# Odd-step cocycle and cycle invariance

`oddSteps` is an additive cocycle along the `T`-orbit: `S_{a+b}(n) = S_a(n) + S_b(T^a n)`.
Consequently the number of odd steps in one period of a `T`-cycle is the same from every
starting point on the cycle.  We also re-export the round-2 cycle bounds with the
minimality witness and the lower bound `971 ≤ S_L` at every point of the cycle.
-/

namespace CollatzSearch
open CollatzProof

/-- **Cocycle.** `S_{a+b}(n) = S_a(n) + S_b(T^a n)`. -/
theorem oddSteps_add (a b n : ℕ) : oddSteps (a + b) n = oddSteps a n + oddSteps b (T^[a] n) := by
  induction a generalizing n with
  | zero => simp [oddSteps]
  | succ a ih =>
    rw [show a + 1 + b = (a + b) + 1 by omega]
    simp only [oddSteps, Function.iterate_succ_apply]
    rw [ih (T n)]
    omega

/-- A point of a `T`-cycle of length `L` returns after `L` steps: `T^L(T^i m) = T^i m`. -/
theorem iterate_cycle {m L : ℕ} (h : T^[L] m = m) (i : ℕ) : T^[L] (T^[i] m) = T^[i] m := by
  rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, h]

/-- **Cycle invariance.** The number of odd steps in a period is the same from every point
of a `T`-cycle: `S_L(T^i m) = S_L(m)`. -/
theorem oddSteps_cycle_invariant {m L : ℕ} (h : T^[L] m = m) (i : ℕ) :
    oddSteps L (T^[i] m) = oddSteps L m := by
  have e1 := oddSteps_add i L m
  have e2 := oddSteps_add L i m
  rw [h, add_comm L i] at e2
  omega

/-- Round-2 cycle bounds with minimality exported: a nontrivial positive `C`-cycle through `n`
has an odd minimum `m` of a `T`-cycle of length `L>0`, with `2^17 ≤ m ≤ n`, `m ≤ T^j m`
for all `j`, `971 ≤ S_L(m) ≤ L`, and `971 ≤ S_L(T^i m)` for every point `T^i m` of the cycle. -/
theorem nontrivial_C_cycle_bounds' (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∃ m L, m % 2 = 1 ∧ 2 ^ 17 ≤ m ∧ m ≤ n ∧ 0 < L ∧
      T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧ 971 ≤ oddSteps L m ∧ oddSteps L m ≤ L ∧
      ∀ i, 971 ≤ oddSteps L (T^[i] m) := by
  obtain ⟨m, L, h1, h2, h3, h4, h5, h6⟩ :=
    exists_min_odd_T_cycle n hn ℓ hℓ h (by omega)
  have hk := oddSteps_ge_of_min_cycle h1 h3 h4 h5
  exact ⟨m, L, h2, min_orbit_ge m h1 h5, h6, h3, h4, h5, hk, oddSteps_le L m,
    fun i => by rw [oddSteps_cycle_invariant h4 i]; exact hk⟩

end CollatzSearch

#print axioms CollatzSearch.oddSteps_add
#print axioms CollatzSearch.iterate_cycle
#print axioms CollatzSearch.oddSteps_cycle_invariant
#print axioms CollatzSearch.nontrivial_C_cycle_bounds'
#print axioms CollatzSearch.descBlock_0
