import Collatz.Milestones
import Farey24
import CycleLenPoly
import Collatz.CycleBasic
import Mathlib.Tactic

/-!
# Instances of the Props M4/M3 of `Milestones.lean`

* `cycleMinAbove_24 : CycleMinAbove (2^24 - 1)` — every element of a nontrivial positive
  `C`-cycle is `≥ 2^24`.
* `cycleLengthAtLeast_31733 : CycleLengthAtLeast 31733` — every nontrivial positive
  `C`-cycle has classical period `ℓ ≥ 31733`.

**Status: CLASSICAL.** Formal instances of Eliahou (1993) at the in-house verified range
`2^24` (kernel sieve `min_orbit_ge_24`, Farey pair `1054/665 < log₂3 < 18403/11611`).
The minimum `m` of the cycle has a `T`-lap `j` with `j + S_j(m) = ℓ` *exactly*
(`exists_T_lap_of_C_cycle`), and the Eliahou decomposition `S_j = 665a + 11611b`,
`j = 1054a + 18403b` (`a, b ≥ 1`) gives `ℓ = 1719a + 30014b ≥ 31733`.

The values `2^24` and `31733` are below the published bounds (cf. Lagarias 1985: 275,000 via
Yoneda's `2^40` verification; Eliahou 1993: 17,087,915).
-/

namespace Collatz
open CollatzProof

/-- **`CycleMinAbove (2^24 − 1)`.** Every positive `C`-periodic `n ∉ {1,2,4}` satisfies
`n ≥ 2^24`. -/
theorem cycleMinAbove_24 : CycleMinAbove (2^24 - 1) := by
  rintro n ⟨hn, ℓ, hℓ, h⟩ h1 h2 h4
  obtain ⟨m, hm0, -, -, hmin, hmn, t, ht⟩ := exists_min_odd_T_cycle_aux' n hn ℓ hℓ h
  have hm1 : m ≠ 1 := by
    rintro rfl
    rcases iterate_C_one_mem t with e | e | e <;> rw [ht] at e <;> contradiction
  have h24 : 2^24 ≤ m := min_orbit_ge_24 (by omega) hmin
  have : (2:ℕ)^24 = 16777216 := by norm_num
  omega

/-- **`CycleLengthAtLeast 31733`.** Every nontrivial positive `C`-cycle has period
`ℓ ≥ 31733 = (1054+18403) + (665+11611)`. -/
theorem cycleLengthAtLeast_31733 : CycleLengthAtLeast 31733 := by
  intro n ℓ hn hℓ h h1 h2 h4
  obtain ⟨m, hm0, hodd, hmℓ, hmin, hmn, t, ht⟩ := exists_min_odd_T_cycle_aux' n hn ℓ hℓ h
  have hm1 : m ≠ 1 := by
    rintro rfl
    rcases iterate_C_one_mem t with e | e | e <;> rw [ht] at e <;> contradiction
  have h24 : 2^24 ≤ m := min_orbit_ge_24 (by omega) hmin
  obtain ⟨j, hj0, -, hjk, hT⟩ := exists_T_lap_of_C_cycle hodd hℓ hmℓ
  obtain ⟨a, b, ha, hb, hk, hL⟩ := cycle_farey_decomp (M := 2^24) (by norm_num) h24 hj0 hT hmin
    (by norm_num : 18403*665 = 1054*11611+1) farey17_low farey24_up
  rw [hk, hL] at hjk
  nlinarith

end Collatz

#print axioms Collatz.cycleMinAbove_24
#print axioms Collatz.cycleLengthAtLeast_31733
