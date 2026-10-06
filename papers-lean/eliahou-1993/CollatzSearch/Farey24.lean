import CollatzSearch.FareyDecomp
import CollatzSearch.Sieve24

/-!
# Farey decomposition at the verified range `2^24`

Combines `descRange_24` (T2) with `cycle_farey_decomp` (T1b) at `M = 2^24` and the Farey pair
`1054/665 < log₂3 < log₂(3 + 2^{-24}) < 18403/11611` (`18403·665 − 1054·11611 = 1`):
every nontrivial `C`-cycle has an odd minimum `m ≥ 2^24` whose `T`-cycle has
`S_L(m) = 665a + 11611b`, `L = 1054a + 18403b` with `a, b ≥ 1`; hence `S_L(m) ≥ 12276` and
`L ≥ 19457`.

A finite formal instance of Eliahou (1993) with a small verified range (the literature's
`2^68` gives `k ≥ 72057431991` by the same theorem).  Not new mathematics; not Goal progress.
-/

namespace CollatzSearch
open CollatzProof

/-- `log₂(3 + 2^{-24}) < 18403/11611` (kernel; ≈ 297k-bit numbers, margin ≈ 5·10⁻⁵ in the
exponent). -/
theorem farey24_up : (3*2^24+1)^11611 < 2^18403 * (2^24)^11611 := by decide +kernel

/-- **T3.** A nontrivial positive `C`-cycle through `n` has an odd minimum `m`,
`2^24 ≤ m ≤ n`, on a `T`-cycle of length `L > 0`, minimal on its orbit, with
`S_L(m) = 665a + 11611b` and `L = 1054a + 18403b` for some `a, b ≥ 1`. -/
theorem nontrivial_C_cycle_farey24 (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∃ m L a b, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧
    T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧ 0 < a ∧ 0 < b ∧ oddSteps L m = 665*a + 11611*b ∧
    L = 1054*a + 18403*b := by
  obtain ⟨m, L, hodd, h17, hmn, hL, hc, hmin, -⟩ := nontrivial_C_cycle_bounds' n hn ℓ hℓ h hne
  have h24 : 2^24 ≤ m := min_orbit_ge_24 (lt_of_lt_of_le (by norm_num) h17) hmin
  obtain ⟨a, b, ha, hb, hk, hLe⟩ := cycle_farey_decomp (M := 2^24) (by norm_num) h24 hL hc hmin
    (by norm_num : 18403*665 = 1054*11611+1) farey17_low farey24_up
  exact ⟨m, L, a, b, hodd, h24, hmn, hL, hc, hmin, ha, hb, by rw [hk]; ring, by rw [hLe]; ring⟩

/-- **T3 corollary.** Same hypotheses: the minimum `m ≥ 2^24` of the cycle has
`12276 ≤ S_L(m)` and `19457 ≤ L`. -/
theorem nontrivial_C_cycle_bounds24 (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∃ m L, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < L ∧
    T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧ 12276 ≤ oddSteps L m ∧ 19457 ≤ L := by
  obtain ⟨m, L, a, b, h1, h2, h3, h4, h5, h6, ha, hb, hk, hL⟩ :=
    nontrivial_C_cycle_farey24 n hn ℓ hℓ h hne
  exact ⟨m, L, h1, h2, h3, h4, h5, h6, by omega, by omega⟩

end CollatzSearch

#print axioms CollatzSearch.farey24_up
#print axioms CollatzSearch.nontrivial_C_cycle_farey24
#print axioms CollatzSearch.nontrivial_C_cycle_bounds24
