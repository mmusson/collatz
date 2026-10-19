/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import Sieve25
import Collatz.MilestoneInstances

/-!
# Kernel-checked published verification bounds

In this file we derive two early published verifications of the Collatz conjecture from the
kernel-checked descent sieve `descRange_25`: Dunn (1973) checked every starting value up to
`22,882,247`, and Coxeter (1971) every starting value up to `500,000`. We also deduce the
corresponding lower bounds for points of a nontrivial cycle.

## Main results

- `reach_one_of_descRange`: if every `m ∈ [2, X)` has a `T`-iterate below `m`, then every
  `n` with `0 < n < X` reaches `1` under `C`.
- `dunn_1973`: every `n` with `1 ≤ n ≤ 22,882,247` reaches `1` under `C`.
- `coxeter_1971`: every `n` with `1 ≤ n ≤ 500,000` reaches `1` under `C`.
- `cycleMinAbove_25`: every positive `C`-periodic `n ∉ {1, 2, 4}` satisfies `2^25 ≤ n`.
- `cycleMinAbove_mono`: `CycleMinAbove` is antitone in the bound.
- `cycleMinAbove_dunn`, `cycleMinAbove_coxeter`: `CycleMinAbove 22882247` and
  `CycleMinAbove 500000`.

## References

- R. Dunn, *On Ulam's problem*, Technical Report CU-CS-011-73, Department of Computer Science,
  University of Colorado, Boulder, 1973.
- H. S. M. Coxeter, *Cyclic sequences and frieze patterns* (The Fourth Felix Behrend Memorial
  Lecture), Vinculum 8 (1971), 4–7.
- J. C. Lagarias, *The 3x+1 problem: an annotated bibliography (1963–1999)*,
  arXiv:math/0309224, entries for Coxeter (1971) and Dunn (1973).
-/

namespace Collatz
open CollatzProof

/-! ### Reaching `1` from descent -/

/-- If `DescRange 2 X`, every `n` with `0 < n < X` reaches `1` under `C`. -/
theorem reach_one_of_descRange {X : ℕ} (hX : DescRange 2 X) :
    ∀ n, 0 < n → n < X → ∃ j, C^[j] n = 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnX
    by_cases h1 : n = 1
    · exact ⟨0, by simp [h1]⟩
    obtain ⟨j, hj⟩ := hX n (by omega) hnX
    obtain ⟨c, hc⟩ := exists_iterate_T_eq_iterate_C j n
    have hpos : 0 < T^[j] n := iterate_T_pos hn j
    rw [hc] at hj hpos
    obtain ⟨j', hj'⟩ := ih _ hj hpos (by omega)
    exact ⟨j' + c, by rw [Function.iterate_add_apply]; exact hj'⟩

/-! ### The published bounds -/

/-- Dunn's verification (1973): every `n` with `1 ≤ n ≤ 22,882,247` reaches `1` under `C`. -/
theorem dunn_1973 : ∀ n, 1 ≤ n → n ≤ 22882247 → ∃ j, C^[j] n = 1 := fun n h1 h2 ↦
  reach_one_of_descRange descRange_25 n h1 (by norm_num; omega)

/-- Coxeter's verification (1971): every `n` with `1 ≤ n ≤ 500,000` reaches `1` under `C`. -/
theorem coxeter_1971 : ∀ n, 1 ≤ n → n ≤ 500000 → ∃ j, C^[j] n = 1 := fun n h1 h2 ↦
  dunn_1973 n h1 (by omega)

/-! ### Lower bounds for cycle points -/

/-- Every positive `C`-periodic `n ∉ {1, 2, 4}` satisfies `2^25 ≤ n`. -/
theorem cycleMinAbove_25 : CycleMinAbove (2^25 - 1) := by
  rintro n ⟨hn, ℓ, hℓ, h⟩ h1 h2 h4
  obtain ⟨m, hm0, -, -, hmin, hmn, t, ht⟩ := exists_min_odd_T_cycle_aux' n hn ℓ hℓ h
  have hm1 : m ≠ 1 := by
    rintro rfl
    rcases iterate_C_one_mem t with e | e | e <;> rw [ht] at e <;> contradiction
  have h25 : 2^25 ≤ m := min_orbit_ge_25 (by omega) hmin
  have : (2:ℕ)^25 = 33554432 := by norm_num
  omega

/-- `CycleMinAbove` is antitone in the bound. -/
theorem cycleMinAbove_mono {B B' : ℕ} (h : B' ≤ B) : CycleMinAbove B → CycleMinAbove B' :=
  fun H n hn h1 h2 h4 ↦ lt_of_le_of_lt h (H n hn h1 h2 h4)

/-- Every point of a nontrivial positive cycle exceeds Dunn's verified range `22,882,247`. -/
theorem cycleMinAbove_dunn : CycleMinAbove 22882247 :=
  cycleMinAbove_mono (by norm_num) cycleMinAbove_25

/-- Every point of a nontrivial positive cycle exceeds Coxeter's verified range `500,000`. -/
theorem cycleMinAbove_coxeter : CycleMinAbove 500000 :=
  cycleMinAbove_mono (by norm_num) cycleMinAbove_25

end Collatz
