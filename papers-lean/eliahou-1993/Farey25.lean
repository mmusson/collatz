import Sieve25
import Collatz.MilestoneInstances

/-!
# Farey decomposition at the verified range `2^25`

With `min_orbit_ge_25` the Eliahou-type Farey pair improves from `18403/11611` (at `2^24`) to
`1054/665 < log₂3 < log₂(3 + 2^{-25}) < 21565/13606` (`21565·665 − 1054·13606 = 1`; the mediant
`22619/14271` lies inside the interval, so this is the Farey pair). Consequences: the odd minimum
`m ≥ 2^25` of a nontrivial cycle has `S_L(m) = 665a + 13606b`, `L = 1054a + 21565b`, `a, b ≥ 1`,
hence `CycleLengthAtLeast 36890` (`36890 = 1054 + 21565 + 665 + 13606`).

Classical (Eliahou 1993 method at a tiny verified range); far below published bounds.
-/

namespace Collatz
open CollatzProof

/-- `log₂(3 + 2^{-25}) < 21565/13606` (kernel, `decide +kernel`). -/
theorem farey25_up : (3*2^25+1)^13606 < 2^21565 * (2^25)^13606 := by decide +kernel

/-- **`CycleLengthAtLeast 36890`.** Every nontrivial positive `C`-cycle has period
`ℓ ≥ 36890 = (1054+21565) + (665+13606)`. -/
theorem cycleLengthAtLeast_36890 : CycleLengthAtLeast 36890 := by
  intro n ℓ hn hℓ h h1 h2 h4
  obtain ⟨m, hm0, hodd, hmℓ, hmin, hmn, t, ht⟩ := exists_min_odd_T_cycle_aux' n hn ℓ hℓ h
  have hm1 : m ≠ 1 := by
    rintro rfl
    rcases iterate_C_one_mem t with e | e | e <;> rw [ht] at e <;> contradiction
  have h25 : 2^25 ≤ m := min_orbit_ge_25 (by omega) hmin
  obtain ⟨j, hj0, -, hjk, hT⟩ := exists_T_lap_of_C_cycle hodd hℓ hmℓ
  obtain ⟨a, b, ha, hb, hk, hL⟩ := cycle_farey_decomp (M := 2^25) (by norm_num) h25 hj0 hT hmin
    (by norm_num : 21565*665 = 1054*13606+1) farey17_low farey25_up
  rw [hk, hL] at hjk
  nlinarith

end Collatz

#print axioms Collatz.farey25_up
#print axioms Collatz.cycleLengthAtLeast_36890
