import CollatzSearch.Sieve25
import CollatzSearch.MilestoneInstances

/-!
# Kernel-checked published verification bounds (Dunn 1973, Coxeter 1971)

* `reach_one_of_descRange` : if every `m ∈ [2, X)` has a `T`-iterate below `m`, then every
  `1 ≤ n < X` reaches `1` under `C` (strong induction; `T`-iterates are `C`-iterates).
* `dunn_1973` : every `1 ≤ n ≤ 22,882,247` reaches `1` under `C`.
  Dunn 1973 (Tech. Rep. CU-CS-011-73, Univ. Colorado; Lagarias annotated bibliography
  math/0309224, entry 51) verified the conjecture up to 22,882,247 (CDC 6400).
* `coxeter_1971` : every `1 ≤ n ≤ 500,000` reaches `1` (Coxeter 1971, entry 41: "tested with an
  electronic computer for all x1 ≤ 500,000").
* `cycleMinAbove_25 : CycleMinAbove (2^25 - 1)`, `cycleMinAbove_mono`,
  `cycleMinAbove_dunn : CycleMinAbove 22882247`, `cycleMinAbove_coxeter : CycleMinAbove 500000`.

All from the kernel sieve `descRange_25` (`decide +kernel` only, checked by the kernel).

**Status.** Claimed as a first formal proof of a published bound, i.e. a *candidate* instance of
M4 in the sense of `Milestones.lean`, SUBJECT TO CRITIC ADJUDICATION (whether a 1973
verification bound counts; whether an earlier formalization exists — unknown). Mathematically
routine, far below the modern `2^68`, and **NOT Goal progress**.
-/

namespace CollatzSearch
open CollatzProof

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

/-- **Dunn (1973), kernel-checked.** Every `n` with `1 ≤ n ≤ 22,882,247` reaches `1` under `C`. -/
theorem dunn_1973 : ∀ n, 1 ≤ n → n ≤ 22882247 → ∃ j, C^[j] n = 1 := fun n h1 h2 =>
  reach_one_of_descRange descRange_25 n h1 (by norm_num; omega)

/-- **Coxeter (1971), kernel-checked.** Every `n` with `1 ≤ n ≤ 500,000` reaches `1` under `C`. -/
theorem coxeter_1971 : ∀ n, 1 ≤ n → n ≤ 500000 → ∃ j, C^[j] n = 1 := fun n h1 h2 =>
  dunn_1973 n h1 (by omega)

/-- **`CycleMinAbove (2^25 − 1)`.** Every positive `C`-periodic `n ∉ {1,2,4}` satisfies
`n ≥ 2^25`. -/
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
  fun H n hn h1 h2 h4 => lt_of_le_of_lt h (H n hn h1 h2 h4)

/-- **`CycleMinAbove 22882247`** (Dunn 1973's verified range). Candidate M4 instance, subject to
critic adjudication. -/
theorem cycleMinAbove_dunn : CycleMinAbove 22882247 :=
  cycleMinAbove_mono (by norm_num) cycleMinAbove_25

/-- **`CycleMinAbove 500000`** (Coxeter 1971's verified range). -/
theorem cycleMinAbove_coxeter : CycleMinAbove 500000 :=
  cycleMinAbove_mono (by norm_num) cycleMinAbove_25

end CollatzSearch

#print axioms CollatzSearch.reach_one_of_descRange
#print axioms CollatzSearch.dunn_1973
#print axioms CollatzSearch.coxeter_1971
#print axioms CollatzSearch.cycleMinAbove_25
#print axioms CollatzSearch.cycleMinAbove_mono
#print axioms CollatzSearch.cycleMinAbove_dunn
#print axioms CollatzSearch.cycleMinAbove_coxeter
