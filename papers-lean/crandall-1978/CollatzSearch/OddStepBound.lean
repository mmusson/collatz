import CollatzSearch.ProductBound
import CollatzSearch.Descent

/-!
# No nontrivial cycle with fewer than 971 odd steps

Formalized instance of the Crandall (1978) / Eliahou (1993) argument.  For the minimum
`m > 1` of a `T`-cycle with `k` odd steps in `L` steps:
* `3^k < 2^L` (`three_pow_lt_two_pow_of_cycle`),
* `2^L m^k ≤ (3m+1)^k` (`cycle_product_bound`), hence `2^L M^k ≤ (3M+1)^k` for `M = 2^17 ≤ m`
  (`min_orbit_ge`, `product_bound_mono`).
A kernel check (`allOK_17`) shows these are incompatible for every `k < 971`.
The check never searches over `L`: for each `k` it verifies `2^(L0-1) ≤ 3^k` and
`(3M+1)^k < 2^L0 M^k` for a computed `L0 = candL k`; soundness does not depend on the
decimal approximation of `log₂ 3` used to compute `L0`.
Not new mathematics; the literature bounds (e.g. Hercher 2023) are far stronger.
-/

namespace CollatzSearch
open CollatzProof

/-- A computed candidate `⌊k · log₂3⌋ + 1` (any value works for soundness). -/
def candL (k : ℕ) : ℕ := k * 1584962500721156 / 10 ^ 15 + 1

/-- Kernel-checkable certificate for one `k`. -/
def kOK (M k : ℕ) : Bool :=
  Nat.ble (2 ^ (candL k - 1)) (3 ^ k) && Nat.blt ((3 * M + 1) ^ k) (2 ^ candL k * M ^ k)

/-- `kOK M k` for all `k < K`. -/
def allOK (M : ℕ) : ℕ → Bool
  | 0 => true
  | K + 1 => allOK M K && kOK M K

/-- If `kOK M k` holds then `(3M+1)^k < 2^L M^k` for every `L` with `3^k < 2^L`. -/
theorem kOK_sound {M k L : ℕ} (hk : kOK M k = true) (h3 : 3 ^ k < 2 ^ L) :
    (3 * M + 1) ^ k < 2 ^ L * M ^ k := by
  simp only [kOK, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq] at hk
  obtain ⟨ha, hb⟩ := hk
  have hL : candL k ≤ L := by
    by_contra hc
    have : 2 ^ L ≤ 2 ^ (candL k - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact lt_of_lt_of_le hb (Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hL))

theorem allOK_sound {M : ℕ} : ∀ K, allOK M K = true → ∀ k, k < K → kOK M k = true := by
  intro K
  induction K with
  | zero => intro _ k hk; omega
  | succ K ih =>
    intro h k hk
    simp only [allOK, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk | rfl
    · exact ih h.1 k hk
    · exact h.2

/-- Kernel-verified certificate for `M = 2^17`, all `k < 971`. -/
theorem allOK_17 : allOK (2 ^ 17) 971 = true := by decide +kernel

/-- **Odd-step bound.** If `m > 1` is the minimum of a `T`-cycle of length `L > 0`, then the
cycle has at least 971 odd steps per period. -/
theorem oddSteps_ge_of_min_cycle {m L : ℕ} (hm1 : 1 < m) (hL : 0 < L)
    (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m) : 971 ≤ oddSteps L m := by
  by_contra hk
  have hM : 2 ^ 17 ≤ m := min_orbit_ge m hm1 hmin
  have h2 := cycle_product_bound (by omega) h hmin
  have h3 := product_bound_mono (M := 2 ^ 17) (by positivity) hM h2
  have h4 := three_pow_lt_two_pow_of_cycle (by omega) hL h
  have h5 := kOK_sound (allOK_sound 971 allOK_17 _ (by omega)) h4
  omega

/-- **C-level corollary.** A positive `C`-periodic point `n ∉ {1,2,4}` yields an odd `m`,
`2^17 ≤ m ≤ n`, on a `T`-cycle of length `L > 0` with `971 ≤ S_L(m) ≤ L`. -/
theorem nontrivial_C_cycle_bounds (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∃ m L, m % 2 = 1 ∧ 2 ^ 17 ≤ m ∧ m ≤ n ∧ 0 < L ∧
      T^[L] m = m ∧ 971 ≤ oddSteps L m ∧ oddSteps L m ≤ L := by
  obtain ⟨m, L, h1, h2, h3, h4, h5, h6⟩ :=
    exists_min_odd_T_cycle n hn ℓ hℓ h (by omega)
  exact ⟨m, L, h2, min_orbit_ge m h1 h5, h6, h3, h4, oddSteps_ge_of_min_cycle h1 h3 h4 h5,
    oddSteps_le L m⟩

end CollatzSearch

#print axioms CollatzSearch.kOK_sound
#print axioms CollatzSearch.allOK_sound
#print axioms CollatzSearch.allOK_17
#print axioms CollatzSearch.oddSteps_ge_of_min_cycle
#print axioms CollatzSearch.nontrivial_C_cycle_bounds
