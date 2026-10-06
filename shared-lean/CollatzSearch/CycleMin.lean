import CollatzSearch.CycleInvariance
import CollatzSearch.Sanity

/-!
# Rotation-free odd-step bound

Removes the rotation/minimality restriction from `oddSteps_ge_of_min_cycle`: **every** point
`x > 0`, `x ∉ {1,2}`, of a `T`-cycle of length `L > 0` has `S_L(x) ≥ 971`.

Proof: pick the cycle minimum `M = T^{j0} x` (`exists_cycle_min`), note `M ≠ 1` (else `x` would
lie on the orbit of `1`, i.e. `x ∈ {1,2}`), apply the round-2 bound at `M`, and transport it back
to `x = T^{L-j0} M` with `oddSteps_cycle_invariant`.  Classical (Crandall/Eliahou type), small range.
-/

namespace CollatzSearch
open CollatzProof

/-- `T` maps positive integers to positive integers. -/
theorem T_pos {x : ℕ} (h : 0 < x) : 0 < T x := by
  unfold T; split_ifs <;> omega

/-- `x > 0 ⇒ T^j x > 0`. -/
theorem iterate_T_pos {x : ℕ} (h : 0 < x) (j : ℕ) : 0 < T^[j] x := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact T_pos ih

/-- Every `T`-cycle through `x` (period `L > 0`) has a point `M = T^{j0} x`, `j0 < L`, which is
the minimum of its orbit and again satisfies `T^L M = M`. -/
theorem exists_cycle_min {x L : ℕ} (hL : 0 < L) (h : T^[L] x = x) :
    ∃ j0 < L, (∀ j, T^[j0] x ≤ T^[j] (T^[j0] x)) ∧ T^[L] (T^[j0] x) = T^[j0] x := by
  classical
  set S := (Finset.range L).image (fun j => T^[j] x) with hS
  have hne : S.Nonempty := ⟨x, Finset.mem_image.2 ⟨0, Finset.mem_range.2 hL, rfl⟩⟩
  obtain ⟨j0, hj0, hj0e⟩ := Finset.mem_image.1 (S.min'_mem hne)
  rw [Finset.mem_range] at hj0
  have hper : Function.IsPeriodicPt T L x := h
  refine ⟨j0, hj0, fun j => ?_, ?_⟩
  · rw [← Function.iterate_add_apply, ← hper.iterate_mod_apply (j + j0), hj0e]
    apply S.min'_le
    exact Finset.mem_image.2 ⟨(j + j0) % L, Finset.mem_range.2 (Nat.mod_lt _ hL), rfl⟩
  · exact iterate_cycle h j0

/-- **Rotation-free odd-step bound.** If `x > 0`, `T^L x = x` with `L > 0`, and `x ∉ {1,2}`,
then `971 ≤ S_L(x)`. -/
theorem oddSteps_ge_of_cycle {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (h : T^[L] x = x)
    (h1 : x ≠ 1) (h2 : x ≠ 2) : 971 ≤ oddSteps L x := by
  obtain ⟨j0, hj0, hmin, hper⟩ := exists_cycle_min hL h
  set M := T^[j0] x with hM
  have hMpos : 0 < M := iterate_T_pos hx j0
  have hxM : T^[L - j0] M = x := by
    rw [hM, ← Function.iterate_add_apply, Nat.sub_add_cancel hj0.le, h]
  have hM1 : M ≠ 1 := by
    intro e
    rw [e] at hxM
    rcases iterate_T_one_mem (L - j0) with e' | e' <;> rw [hxM] at e' <;> contradiction
  have hb := oddSteps_ge_of_min_cycle (by omega) hL hper hmin
  have hi := oddSteps_cycle_invariant hper (L - j0)
  rw [hxM] at hi
  omega

end CollatzSearch

#print axioms CollatzSearch.T_pos
#print axioms CollatzSearch.iterate_T_pos
#print axioms CollatzSearch.exists_cycle_min
#print axioms CollatzSearch.oddSteps_ge_of_cycle
