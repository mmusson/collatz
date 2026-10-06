import CollatzSearch.CycleBasic
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# The maximum of a Collatz cycle — classical folklore, NOT Goal progress

Unconditional structural facts about the **maximum** of a positive cycle (the library already
had facts about the minimum, `CycleMin.lean`, and about multiples of 3, `Mod3.lean`):

* `T_cycle_max_structure`: on a positive `T`-cycle the maximum `M` satisfies `M ≡ 2 (mod 6)`;
  its orbit predecessor `y` is `≡ 1 (mod 4)` and `2M = 3y + 1`.
* `C_cycle_max_mod12`: on a positive `C`-cycle the maximum `N` satisfies `N ≡ 4 (mod 12)`;
  its predecessor `z` is odd and `N = 3z + 1`.

Proved directly for each map (no `C ↔ T` transfer). Trivial cycles check it: `T`: `{1,2}`,
max `2`, predecessor `1`; `C`: `{1,4,2}`, max `4`, predecessor `1`.

This is folklore. It does **not** advance `no_nontrivial_cycles`, which remains OPEN.
-/

namespace CollatzSearch
open CollatzProof

/-- A periodic orbit of `f : ℕ → ℕ` (period `L > 0`) attains its maximum at some `j < L`, and
that value bounds **every** iterate `f^[i] x` (all `i`, not only `i < L`). -/
theorem exists_orbit_max (f : ℕ → ℕ) {x L : ℕ} (hL : 0 < L) (h : f^[L] x = x) :
    ∃ j, j < L ∧ ∀ i, f^[i] x ≤ f^[j] x := by
  have hne : (Finset.range L).Nonempty := ⟨0, Finset.mem_range.2 hL⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image (Finset.range L) (fun i => f^[i] x) hne
  refine ⟨j, Finset.mem_range.1 hj, fun i => ?_⟩
  have hp : Function.IsPeriodicPt f L x := h
  rw [← hp.iterate_mod_apply]
  exact hmax _ (Finset.mem_range.2 (Nat.mod_lt _ hL))

/-- On a periodic orbit (period `L > 0`), `f^[j+L-1] x` is an `f`-preimage of `f^[j] x`. -/
theorem iterate_pred_apply (f : ℕ → ℕ) {x L : ℕ} (hL : 0 < L) (h : f^[L] x = x) (j : ℕ) :
    f (f^[j + L - 1] x) = f^[j] x := by
  rw [← Function.iterate_succ_apply' f, show (j + L - 1).succ = j + L by omega,
    Function.iterate_add_apply, h]

private theorem T_pos_cmax {x : ℕ} (h : 0 < x) : 0 < T x := by
  unfold T; split_ifs <;> omega

private theorem iterate_T_pos_cmax {x : ℕ} (h : 0 < x) (j : ℕ) : 0 < T^[j] x := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact T_pos_cmax ih

/-- **Maximum of a `T`-cycle** (folklore). If `x > 0`, `L > 0`, `T^L x = x`, then some orbit
point `M = T^j x` is `≥` every `T^i x`, `M % 6 = 2`, and its orbit predecessor
`y = T^{j+L-1} x` satisfies `T y = M`, `y % 4 = 1`, `2M = 3y + 1`. -/
theorem T_cycle_max_structure {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (h : T^[L] x = x) :
    ∃ j M y, T^[j] x = M ∧ (∀ i, T^[i] x ≤ M) ∧ M % 6 = 2 ∧
      T^[j + L - 1] x = y ∧ T y = M ∧ y % 4 = 1 ∧ 2 * M = 3 * y + 1 := by
  obtain ⟨j, -, hmax⟩ := exists_orbit_max T hL h
  refine ⟨j, T^[j] x, T^[j + L - 1] x, rfl, hmax, ?_⟩
  set M := T^[j] x
  set y := T^[j + L - 1] x
  have hTy : T y = M := iterate_pred_apply T hL h j
  have hyle : y ≤ M := hmax _
  have hypos : 0 < y := iterate_T_pos_cmax hx _
  have hTM : T M ≤ M := by
    have := hmax (j + 1); rwa [Function.iterate_succ_apply'] at this
  have hMev : M % 2 = 0 := by
    by_contra hc; unfold T at hTM; split_ifs at hTM; omega
  have h2 : 2 * M = 3 * y + 1 := by
    unfold T at hTy; split_ifs at hTy <;> omega
  exact ⟨by omega, rfl, hTy, by omega, h2⟩

/-- **Maximum of a `C`-cycle** (folklore). If `n > 0`, `ℓ > 0`, `C^ℓ n = n`, then some orbit
point `N = C^j n` is `≥` every `C^i n`, `N % 12 = 4`, and its predecessor `z = C^{j+ℓ-1} n`
is odd with `N = 3z + 1`. -/
theorem C_cycle_max_mod12 {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) :
    ∃ j N z, C^[j] n = N ∧ (∀ i, C^[i] n ≤ N) ∧ N % 12 = 4 ∧
      C^[j + ℓ - 1] n = z ∧ z % 2 = 1 ∧ N = 3 * z + 1 := by
  obtain ⟨j, -, hmax⟩ := exists_orbit_max C hℓ h
  refine ⟨j, C^[j] n, C^[j + ℓ - 1] n, rfl, hmax, ?_⟩
  set N := C^[j] n
  set z := C^[j + ℓ - 1] n
  have hCz : C z = N := iterate_pred_apply C hℓ h j
  have hzle : z ≤ N := hmax _
  have hzpos : 0 < z := iterate_C_pos hn _
  have h1 : C N ≤ N := by
    have := hmax (j + 1); rwa [Function.iterate_succ_apply'] at this
  have h2 : C (C N) ≤ N := by
    have := hmax (j + 2)
    rwa [Function.iterate_succ_apply', Function.iterate_succ_apply'] at this
  have hNev : N % 2 = 0 := by
    by_contra hc; unfold C at h1; split_ifs at h1; omega
  have hzodd : z % 2 = 1 := by
    by_contra hc; unfold C at hCz; split_ifs at hCz <;> omega
  have hN3 : N = 3 * z + 1 := by
    unfold C at hCz; split_ifs at hCz <;> omega
  have hCN : C N = N / 2 := by unfold C; simp [hNev]
  rw [hCN] at h2
  have hN4 : N % 4 = 0 := by
    by_contra hc; unfold C at h2; split_ifs at h2 <;> omega
  exact ⟨by omega, rfl, hzodd, hN3⟩

/-- Sanity (`T`, cycle `{1,2}`): `x = 1`, `L = 2`, max `2 = T 1` at `j = 1`, predecessor
`T^[2] 1 = 1`. -/
example : T^[2] 1 = 1 ∧ T^[1] 1 = 2 ∧ T^[1 + 2 - 1] 1 = 1 ∧ 2 * 2 = 3 * 1 + 1 := by decide

/-- Sanity (`C`, cycle `{1,4,2}`): max `4 = C 1` at `j = 1`, predecessor `C^[3] 1 = 1`. -/
example : C^[3] 1 = 1 ∧ C^[1] 1 = 4 ∧ C^[1 + 3 - 1] 1 = 1 ∧ 4 % 12 = 4 := by decide

end CollatzSearch

#print axioms CollatzSearch.exists_orbit_max
#print axioms CollatzSearch.iterate_pred_apply
#print axioms CollatzSearch.T_cycle_max_structure
#print axioms CollatzSearch.C_cycle_max_mod12
