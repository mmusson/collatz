import CollatzProof.Equivalence
import Mathlib.Dynamics.PeriodicPts.Defs
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Cycle infrastructure

Reduction of the no-nontrivial-cycles statement (about `C`-cycles) to a statement
about the *minimal element* of a `T`-cycle, which is necessarily odd and `> 1`.

## Main results
* `goal_of_no_min_odd_T_cycle` — if no odd `m > 1` is the minimum of a `T`-cycle through
  `m`, then every positive `C`-periodic point lies in `{1,2,4}`.
* `exists_min_odd_T_cycle` — unconditional: a nontrivial positive `C`-cycle point `n`
  yields an odd `m > 1`, `m ≤ n`, which is the minimum of a `T`-cycle through `m`.
-/

namespace Collatz
open CollatzProof

/-- `C` maps positive integers to positive integers. -/
theorem C_pos {n : ℕ} (hn : 0 < n) : 0 < C n := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [C_of_even h]; omega
  · rw [C_of_odd h]; omega

/-- Every `C`-iterate of a positive integer is positive. -/
theorem iterate_C_pos {n : ℕ} (hn : 0 < n) (j : ℕ) : 0 < C^[j] n := by
  induction j with
  | zero => simpa using hn
  | succ j ih => rw [Function.iterate_succ_apply']; exact C_pos ih

/-- The `C`-orbit of `1` is contained in `{1,2,4}`. -/
theorem iterate_C_one_mem (i : ℕ) : C^[i] 1 = 1 ∨ C^[i] 1 = 2 ∨ C^[i] 1 = 4 := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h | h <;> rw [h] <;> decide

/-- Every `T`-iterate is a `C`-iterate: `T^j x = C^i x` for some `i`. -/
theorem exists_iterate_T_eq_iterate_C (j x : ℕ) : ∃ i, T^[j] x = C^[i] x := by
  induction j generalizing x with
  | zero => exact ⟨0, rfl⟩
  | succ j ih =>
    obtain ⟨e, -, he⟩ := exists_iterate_C_eq_T x
    obtain ⟨i', hi'⟩ := ih (T x)
    refine ⟨i' + e, ?_⟩
    rw [Function.iterate_succ_apply, hi', he, Function.iterate_add_apply]

/-- **Lemma B (lifting).** If `i = 0` or `C^{i-1} x` is even (i.e. the `i`-th `C`-step is
a halving), then `C^i x = T^j x` for some `j ≤ i`, with `j > 0` when `i > 0`. -/
theorem exists_iterate_T_of_C (i x : ℕ) (hi : ∀ i', i = i' + 1 → C^[i'] x % 2 = 0) :
    ∃ j, j ≤ i ∧ (0 < i → 0 < j) ∧ T^[j] x = C^[i] x := by
  induction i using Nat.strong_induction_on generalizing x with
  | _ i ih =>
    match i, ih, hi with
    | 0, _, _ => exact ⟨0, le_rfl, by simp, rfl⟩
    | i' + 1, ih, hi =>
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx
      · -- even: T x = C x
        obtain ⟨j', hj', -, hT⟩ := ih i' (by omega) (C x) (by
          intro i'' hi''
          have := hi i' rfl
          rw [hi'', Function.iterate_succ_apply] at this
          exact this)
        refine ⟨j' + 1, by omega, fun _ => by omega, ?_⟩
        rw [Function.iterate_succ_apply, T_eq_C_of_even hx, hT, ← Function.iterate_succ_apply]
      · match i', ih, hi with
        | 0, _, hi =>
          have := hi 0 rfl
          simp at this; omega
        | i'' + 1, ih, hi =>
          obtain ⟨j'', hj'', -, hT⟩ := ih i'' (by omega) (C (C x)) (by
            intro k hk
            have := hi (i'' + 1) rfl
            rw [hk, show k + 1 + 1 = k + 2 by ring, Function.iterate_add_apply] at this
            exact this)
          refine ⟨j'' + 1, by omega, fun _ => by omega, ?_⟩
          rw [Function.iterate_succ_apply, T_eq_C_C_of_odd hx, hT, ← iterate_C_two,
            ← Function.iterate_add_apply]

/-- Structural core: from a positive `C`-cycle point `n` (period `ℓ > 0`) we get the
minimum `m` of its orbit, which is odd, satisfies `m ≤ n`, has `n` on its `C`-orbit,
and lies on a `T`-cycle of which it is the minimum. -/
theorem exists_min_odd_T_cycle_aux (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) :
    ∃ m L, 0 < m ∧ m % 2 = 1 ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧ m ≤ n ∧
      ∃ t, C^[t] m = n := by
  have hne : (Finset.range ℓ).Nonempty := ⟨0, by simpa using hℓ⟩
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image (Finset.range ℓ) (fun j => C^[j] n) hne
  rw [Finset.mem_range] at hj0
  set m := C^[j0] n with hm
  have hper : Function.IsPeriodicPt C ℓ n := h
  -- Step 1
  have h1 : ∀ t, m ≤ C^[t] n := by
    intro t
    rw [← hper.iterate_mod_apply]
    exact hmin _ (Finset.mem_range.2 (Nat.mod_lt _ hℓ))
  -- Step 2
  have h2 : ∀ t, m ≤ C^[t] m := by
    intro t; rw [hm, ← Function.iterate_add_apply]; exact h1 _
  have hmℓ : C^[ℓ] m = m := by
    rw [hm, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, h]
  -- Step 3
  have hmpos : 0 < m := iterate_C_pos hn j0
  have hmodd : m % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · have := h2 1
      rw [Function.iterate_one, C_of_even he] at this
      omega
    · exact ho
  -- Step 4
  have hback : C^[ℓ - j0] m = n := by
    rw [hm, ← Function.iterate_add_apply, Nat.sub_add_cancel hj0.le, h]
  have hmn : m ≤ n := by simpa using h1 0
  -- Step 5
  obtain ⟨L, -, hLpos, hL⟩ := exists_iterate_T_of_C ℓ m (by
    intro i hi
    rcases Nat.mod_two_eq_zero_or_one (C^[i] m) with he | ho
    · exact he
    · exfalso
      have := hmℓ
      rw [hi, Function.iterate_succ_apply', C_of_odd ho] at this
      omega)
  refine ⟨m, L, hmpos, hmodd, hLpos hℓ, hL.trans hmℓ, ?_, hmn, _, hback⟩
  -- Step 6
  intro j
  obtain ⟨i, hi⟩ := exists_iterate_T_eq_iterate_C j m
  rw [hi]; exact h2 i

/-- A positive `C`-cycle point outside `{1,2,4}` yields an odd `m > 1`, `m ≤ n`, which is
the minimum of a `T`-cycle through `m`. -/
theorem exists_min_odd_T_cycle (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : ¬ (n = 1 ∨ n = 2 ∨ n = 4)) :
    ∃ m L, 1 < m ∧ m % 2 = 1 ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧ m ≤ n := by
  obtain ⟨m, L, hmpos, hmodd, hL, hLm, hmin, hmn, t, ht⟩ :=
    exists_min_odd_T_cycle_aux n hn ℓ hℓ h
  refine ⟨m, L, ?_, hmodd, hL, hLm, hmin, hmn⟩
  by_contra h1
  obtain rfl : m = 1 := by omega
  exact hne (ht ▸ iterate_C_one_mem t)

/-- **Reduction.** If no odd `m > 1` is the minimum of a `T`-cycle through `m`, then every
positive `C`-periodic point lies in `{1,2,4}`. -/
theorem goal_of_no_min_odd_T_cycle
    (H : ∀ m L : ℕ, 1 < m → m % 2 = 1 → 0 < L → T^[L] m = m → (∀ j, m ≤ T^[j] m) → False)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) : n = 1 ∨ n = 2 ∨ n = 4 := by
  by_contra hne
  obtain ⟨m, L, h1, h2, h3, h4, h5, -⟩ := exists_min_odd_T_cycle n hn ℓ hℓ h hne
  exact H m L h1 h2 h3 h4 h5

end Collatz

#print axioms Collatz.iterate_C_one_mem
#print axioms Collatz.exists_iterate_T_of_C
#print axioms Collatz.exists_min_odd_T_cycle
#print axioms Collatz.goal_of_no_min_odd_T_cycle
#print axioms Collatz.C_pos
#print axioms Collatz.iterate_C_pos
#print axioms Collatz.exists_iterate_T_eq_iterate_C
#print axioms Collatz.exists_min_odd_T_cycle_aux
