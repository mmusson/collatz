import CollatzSearch.FiniteRuns
import CollatzSearch.Diophantine
import CollatzSearch.CRuns
import Mathlib.Tactic

/-!
# The minimum of a Collatz cycle is polynomial in its length; polynomially many
# Cycles of bounded length

**Status: Unconditional.** Ingredients are classical: the Crandall (1978) / Eliahou (1993)
minimum bound `3m(2^L − 3^k) ≤ k 2^L` (`cycle_diophantine`, `CycleInvariance`/`Diophantine`) plus an effective
irrationality measure of `log₂ 3` (in the role of Rhin 1987; here the in-house two-regime
gap: `gapBelow_big` (`FareyBigCore`/`FareyBigCond`) for `k < K1big ≈ 3.15·10^50` and the elementary Padé measure
`linFormHyp_uncond` (`PadeSup`/`FewRunsUncond`/55) for `k ≥ 2^100`). Status (`MilestoneInstances`/`CycleLenPoly` critics): **known/folklore** (Crandall 1978 minimum bound + effective
irrationality measure of `log₂ 3`, cf. Rhin 1987; Belaga–Mignotte-type bounds); first
formalization in this library.

**NOT Goal progress.** `no_nontrivial_cycles`, `FinitelyManyCycles` and `AtMostCycles` remain
OPEN: the bound grows with the length. The exponent 342 is crude; for `k < K1big` alone the
proof gives `3m ≤ 2^170 k`, i.e. linear in the length.

* `gap_all`: `0 < k`, `3^k < 2^L` ⇒ `2^L ≤ 2^172 k^341 (2^L − 3^k)` (every `k`).
* `three_min_le_of_cycle`: `3m(2^L − 3^k) ≤ k 2^L` for the `T`-orbit minimum (ℕ-subtraction).
* `min_le_poly_period`: odd `T`-orbit minimum `m` of a `T`-cycle of length `L > 0` ⇒
  `m ≤ 2^171 L^342`.
* `exists_T_lap_of_C_cycle`: an odd `C`-periodic `m` with `C^ℓ m = m` has a `T`-lap `j`,
  `0 < j ≤ ℓ`, with `j + S_j(m) = ℓ` exactly.
* `C_cycle_min_le_poly`, `cycleMinima_le_poly`: the same bound at the `C` level, with `ℓ`.
* `cycleMinima_len_le_subset`, `finite_cycleMinima_len_le`: cycles having a `C`-period
  `≤ N` have minimum `≤ 2^171 N^342`; there are at most `2^171 N^342 + 1` of them
  (vs. the trivial `2^(N+1)` of `perUpTo_finite_ncard`).
* `cycleMinima_minimalPeriod_le_subset`, `finite_cycleMinima_minimalPeriod_le`: same for
  minimal `T`-period `≤ N`.
-/

namespace CollatzSearch
open CollatzProof

/-- **Effective gap for all `k`.** If `0 < k` and `3^k < 2^L` then
`2^L ≤ 2^172 k^341 (2^L − 3^k)`. Case `k < 2^100 < K1big`: `gapBelow_big`; case `k ≥ 2^100`:
`linFormHyp_uncond`. -/
theorem gap_all {k L : ℕ} (hk : 0 < k) (h3 : 3^k < 2^L) :
    2^L ≤ 2^172 * k^341 * (2^L - 3^k) := by
  have hk1 : 1 ≤ k^341 := Nat.one_le_pow _ _ hk
  rcases lt_or_ge k (2^100) with hlt | hge
  · have hK : k < K1big := lt_of_lt_of_le hlt (by norm_num [K1big])
    have := gapBelow_big k L hk hK h3
    calc 2^L ≤ 2^170 * (2^L - 3^k) := this
      _ ≤ 2^172 * k^341 * (2^L - 3^k) := by
        apply Nat.mul_le_mul_right
        calc 2^170 = 2^170 * 1 := by ring
          _ ≤ 2^172 * k^341 := Nat.mul_le_mul (by norm_num) hk1
  · have := linFormHyp_uncond k L hge h3
    calc 2^L ≤ 2^2 * k^341 * (2^L - 3^k) := this
      _ ≤ 2^172 * k^341 * (2^L - 3^k) := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; norm_num

/-- **Crandall/Eliahou minimum bound (ℕ-subtraction form).** For the minimum `m > 0` of a
`T`-cycle of length `L`, `3m(2^L − 3^k) ≤ k 2^L` with `k = S_L(m)`. -/
theorem three_min_le_of_cycle {m L : ℕ} (hm : 0 < m) (hc : T^[L] m = m)
    (hmin : ∀ j, m ≤ T^[j] m) :
    3*m*(2^L - 3^(oddSteps L m)) ≤ oddSteps L m * 2^L := by
  have h := cycle_diophantine hm hc hmin
  rw [Nat.mul_sub]
  have e1 : 3*m*2^L = 2^L*(3*m) := by ring
  have e2 : 3*m*3^(oddSteps L m) = 3^(oddSteps L m)*(3*m) := by ring
  rw [e1, e2]
  omega

/-- **Minimum polynomial in the length (T level).** If `m` is odd and minimal on its
`T`-orbit, `L > 0` and `T^L m = m`, then `m ≤ 2^171 L^342`. -/
theorem min_le_poly_period {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) : m ≤ 2^171 * L^342 := by
  have hm : 0 < m := by omega
  set k := oddSteps L m with hkdef
  have h3 : 3^k < 2^L := three_pow_lt_two_pow_of_cycle hm hL hc
  have hk0 : 0 < k := oddSteps_pos_of_cycle hm hL hc
  have hkL : k ≤ L := oddSteps_le L m
  have hd : 0 < 2^L - 3^k := by omega
  have h1 := three_min_le_of_cycle hm hc hmin
  have h0 := gap_all hk0 h3
  have h2 : 3*m*(2^L - 3^k) ≤ (2^172*k^342)*(2^L - 3^k) := by
    calc 3*m*(2^L - 3^k) ≤ k * 2^L := h1
      _ ≤ k * (2^172 * k^341 * (2^L - 3^k)) := Nat.mul_le_mul_left _ h0
      _ = (2^172*k^342)*(2^L - 3^k) := by ring
  have h4 : 3*m ≤ 2^172*k^342 := Nat.le_of_mul_le_mul_right h2 hd
  have h5 : k^342 ≤ L^342 := Nat.pow_le_pow_left hkL _
  have h6 : 3*m ≤ 2*(2^171*L^342) := by
    calc 3*m ≤ 2^172*k^342 := h4
      _ ≤ 2^172*L^342 := Nat.mul_le_mul_left _ h5
      _ = 2*(2^171*L^342) := by ring
  generalize 2^171*L^342 = X at h6 ⊢
  omega

/-- The `C`-predecessor of an odd `C`-periodic point is even (else its image `3y+1` is even). -/
theorem pred_even_of_C_cycle {m ℓ : ℕ} (hodd : m % 2 = 1) (h : C^[ℓ] m = m) :
    ∀ i', ℓ = i' + 1 → C^[i'] m % 2 = 0 := by
  intro i' hi
  subst hi
  rw [Function.iterate_succ_apply'] at h
  set y := C^[i'] m
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy
  · exact hy
  · exfalso
    have : C y = 3*y+1 := by unfold C; simp [hy]
    omega

/-- An odd `C`-periodic point `m` (`C^ℓ m = m`, `ℓ > 0`) has a `T`-lap `j` with `0 < j ≤ ℓ`,
`j + S_j(m) = ℓ` exactly and `T^j m = m`. -/
theorem exists_T_lap_of_C_cycle {m ℓ : ℕ} (hodd : m % 2 = 1) (hℓ : 0 < ℓ) (h : C^[ℓ] m = m) :
    ∃ j, 0 < j ∧ j ≤ ℓ ∧ j + oddSteps j m = ℓ ∧ T^[j] m = m := by
  obtain ⟨j, hj, hT⟩ := exists_iterate_T_of_C_exact ℓ m (pred_even_of_C_cycle hodd h)
  rw [h] at hT
  refine ⟨j, ?_, by omega, hj, hT⟩
  rcases Nat.eq_zero_or_pos j with h0 | h0
  · subst h0; simp [oddSteps] at hj; omega
  · exact h0

/-- **C level.** A positive `C`-cycle of length `ℓ > 0` through `n` contains an odd point
`m ≤ n` (`C^t m = n`, `C^ℓ m = m`) with `m ≤ 2^171 ℓ^342`. -/
theorem C_cycle_min_le_poly (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) :
    ∃ m, m % 2 = 1 ∧ m ≤ n ∧ (∃ t, C^[t] m = n) ∧ C^[ℓ] m = m ∧ m ≤ 2^171 * ℓ^342 := by
  obtain ⟨m, -, hodd, hmℓ, hmin, hmn, t, ht⟩ := exists_min_odd_T_cycle_aux' n hn ℓ hℓ h
  obtain ⟨j, hj0, hjℓ, -, hT⟩ := exists_T_lap_of_C_cycle hodd hℓ hmℓ
  refine ⟨m, hodd, hmn, ⟨t, ht⟩, hmℓ, ?_⟩
  calc m ≤ 2^171 * j^342 := min_le_poly_period hodd hmin hj0 hT
    _ ≤ 2^171 * ℓ^342 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hjℓ _)

/-- A cycle minimum `n ∈ CycleMinima` with `C^ℓ n = n`, `ℓ > 0` satisfies `n ≤ 2^171 ℓ^342`. -/
theorem cycleMinima_le_poly {n ℓ : ℕ} (hmem : n ∈ CycleMinima) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) :
    n ≤ 2^171 * ℓ^342 := by
  obtain ⟨⟨hn, -⟩, hminC⟩ := hmem
  obtain ⟨m, -, hmn, ⟨t, ht⟩, hmℓ, hb⟩ := C_cycle_min_le_poly n hn ℓ hℓ h
  have per : C^[ℓ * t] m = m := (Function.IsPeriodicPt.mul_const (show Function.IsPeriodicPt C ℓ m from hmℓ) t).eq
  have hle : t ≤ ℓ * t := Nat.le_mul_of_pos_left t hℓ
  have hback : C^[ℓ * t - t] n = m := by
    rw [← ht, ← Function.iterate_add_apply, Nat.sub_add_cancel hle, per]
  have hnm : n ≤ m := by have := hminC (ℓ * t - t); rwa [hback] at this
  omega

/-- Cycle minima having some `C`-period `ℓ ∈ (0, N]` lie in `[0, 2^171 N^342]`. -/
theorem cycleMinima_len_le_subset (N : ℕ) :
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n} ⊆ Set.Iic (2^171 * N^342) := by
  rintro n ⟨hmem, ℓ, hℓ, hℓN, h⟩
  exact le_trans (cycleMinima_le_poly hmem hℓ h)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hℓN _))

/-- `|[0, B]| = B + 1` in ℕ. -/
theorem ncard_Iic_nat (B : ℕ) : (Set.Iic B).ncard = B + 1 := by
  have : Set.Iic B = ↑(Finset.range (B+1)) := by
    ext x; simp
  rw [this, Set.ncard_coe_finset, Finset.card_range]

/-- **Polynomial count of cycles of bounded length.** For every `N`, the set of cycles (as
minima) having a `C`-period `≤ N` is finite with at most `2^171 N^342 + 1` elements. Compare the
trivial `2^(N+1)`. `FinitelyManyCycles` remains OPEN. -/
theorem finite_cycleMinima_len_le (N : ℕ) :
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.Finite ∧
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.ncard ≤ 2^171 * N^342 + 1 := by
  refine ⟨(Set.finite_Iic _).subset (cycleMinima_len_le_subset N), ?_⟩
  calc _ ≤ (Set.Iic (2^171 * N^342)).ncard :=
        Set.ncard_le_ncard (cycleMinima_len_le_subset N) (Set.finite_Iic _)
    _ = 2^171 * N^342 + 1 := ncard_Iic_nat _

/-- Cycle minima with minimal `T`-period `≤ N` lie in `[0, 2^171 N^342]`. -/
theorem cycleMinima_minimalPeriod_le_subset (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N} ⊆ Set.Iic (2^171 * N^342) := by
  rintro n ⟨hmem, hN⟩
  obtain ⟨hodd, hmin, L, hL, hc⟩ := cycleMinima_T_props hmem
  have hpos : 0 < Function.minimalPeriod T n :=
    Function.minimalPeriod_pos_of_mem_periodicPts ⟨L, hL, hc⟩
  have := min_le_poly_period hodd hmin hpos (Function.iterate_minimalPeriod (f := T) (x := n))
  exact le_trans this (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN _))

/-- Cycles (as minima) with minimal `T`-period `≤ N`: finitely many, at most
`2^171 N^342 + 1`. -/
theorem finite_cycleMinima_minimalPeriod_le (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.Finite ∧
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.ncard ≤ 2^171 * N^342 + 1 := by
  refine ⟨(Set.finite_Iic _).subset (cycleMinima_minimalPeriod_le_subset N), ?_⟩
  calc _ ≤ (Set.Iic (2^171 * N^342)).ncard :=
        Set.ncard_le_ncard (cycleMinima_minimalPeriod_le_subset N) (Set.finite_Iic _)
    _ = 2^171 * N^342 + 1 := ncard_Iic_nat _

end CollatzSearch

#print axioms CollatzSearch.gap_all
#print axioms CollatzSearch.three_min_le_of_cycle
#print axioms CollatzSearch.min_le_poly_period
#print axioms CollatzSearch.exists_T_lap_of_C_cycle
#print axioms CollatzSearch.C_cycle_min_le_poly
#print axioms CollatzSearch.cycleMinima_le_poly
#print axioms CollatzSearch.cycleMinima_len_le_subset
#print axioms CollatzSearch.finite_cycleMinima_len_le
#print axioms CollatzSearch.cycleMinima_minimalPeriod_le_subset
#print axioms CollatzSearch.finite_cycleMinima_minimalPeriod_le
#print axioms CollatzSearch.pred_even_of_C_cycle
#print axioms CollatzSearch.ncard_Iic_nat
