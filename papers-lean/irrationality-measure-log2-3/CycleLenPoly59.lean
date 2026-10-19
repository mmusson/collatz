/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import CycleLenPoly
import PadeCheb

/-!
# The minimum of a Collatz cycle is at most `2^171 L^59`

In this file we lower the exponent `342` of `CycleLenPoly` to `59`, using the explicit
irrationality measure `linFormHyp_58` of `PadeCheb` instead of the weaker Padé measure. The
effective gap `2^L ≤ 2^172 k^58 (2^L - 3^k)` holds for every `k`: for `k < 2^167` it follows from
`gapBelow_K1big`, and for `k ≥ 2^167` from `linFormHyp_58`. Combined with Crandall's bound
`3m (2^L - 3^k) ≤ k 2^L`, the minimum `m` of a `T`-cycle of length `L` satisfies
`m ≤ 2^171 L^59`.

## Main results

- `gap_all59`: if `0 < k` and `3^k < 2^L`, then `2^L ≤ 2^172 k^58 (2^L - 3^k)`.
- `min_le_poly_period59`: the odd minimum `m` of a `T`-cycle of length `L > 0` satisfies
  `m ≤ 2^171 L^59`.
- `C_cycle_min_le_poly59`, `cycleMinima_le_poly59`: the same bound for `C`-cycles of length `ℓ`.
- `finite_cycleMinima_len_le59`, `ncard_cycleMinima_len_le59`: at most `2^171 N^59 + 1` cycles
  have a `C`-period at most `N`.
- `finite_cycleMinima_minimalPeriod_le59`, `ncard_cycleMinima_minimalPeriod_le59`: the same for
  minimal `T`-period at most `N`.

## References

- R. E. Crandall, *On the "3x+1" problem*, Math. Comp. 32 (1978), 1281–1292.
- G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Séminaire de Théorie des
  Nombres, Paris 1985–86, Progr. Math. 71, Birkhäuser (1987), 155–164.
-/

namespace Collatz
open CollatzProof

/-! ### The minimum of a cycle -/

/-- Effective gap for all `k`: if `0 < k` and `3^k < 2^L`, then
`2^L ≤ 2^172 k^58 (2^L − 3^k)`. -/
theorem gap_all59 {k L : ℕ} (hk : 0 < k) (h3 : 3^k < 2^L) :
    2^L ≤ 2^172 * k^58 * (2^L - 3^k) := by
  have hk1 : 1 ≤ k^58 := Nat.one_le_pow _ _ hk
  rcases lt_or_ge k (2^167) with hlt | hge
  · have hK : k < K1big := lt_of_lt_of_le hlt (by norm_num [K1big])
    have := gapBelow_K1big k L hk hK h3
    calc 2^L ≤ 2^170 * (2^L - 3^k) := this
      _ ≤ 2^172 * k^58 * (2^L - 3^k) := by
        apply Nat.mul_le_mul_right
        calc 2^170 = 2^170 * 1 := by ring
          _ ≤ 2^172 * k^58 := Nat.mul_le_mul (by norm_num) hk1
  · have := linFormHyp_58 k L hge h3
    calc 2^L ≤ 2^2 * k^58 * (2^L - 3^k) := this
      _ ≤ 2^172 * k^58 * (2^L - 3^k) := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; norm_num

/-- The minimum of a `T`-cycle is polynomial in its length: if `m` is odd and minimal on its
`T`-orbit, `L > 0` and `T^L m = m`, then `m ≤ 2^171 L^59`. -/
theorem min_le_poly_period59 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) : m ≤ 2^171 * L^59 := by
  have hm : 0 < m := by omega
  set k := oddSteps L m with hkdef
  have h3 : 3^k < 2^L := three_pow_lt_two_pow_of_cycle hm hL hc
  have hk0 : 0 < k := oddSteps_pos_of_cycle hm hL hc
  have hkL : k ≤ L := oddSteps_le L m
  have hd : 0 < 2^L - 3^k := by omega
  have h1 := three_min_le_of_cycle hm hc hmin
  have h0 := gap_all59 hk0 h3
  have h2 : 3*m*(2^L - 3^k) ≤ (2^172*k^59)*(2^L - 3^k) := by
    calc 3*m*(2^L - 3^k) ≤ k * 2^L := h1
      _ ≤ k * (2^172 * k^58 * (2^L - 3^k)) := Nat.mul_le_mul_left _ h0
      _ = (2^172*k^59)*(2^L - 3^k) := by ring
  have h4 : 3*m ≤ 2^172*k^59 := Nat.le_of_mul_le_mul_right h2 hd
  have h5 : k^59 ≤ L^59 := Nat.pow_le_pow_left hkL _
  have h6 : 3*m ≤ 2*(2^171*L^59) := by
    calc 3*m ≤ 2^172*k^59 := h4
      _ ≤ 2^172*L^59 := Nat.mul_le_mul_left _ h5
      _ = 2*(2^171*L^59) := by ring
  generalize 2^171*L^59 = X at h6 ⊢
  omega

/-- A positive `C`-cycle of length `ℓ > 0` through `n` contains an odd point
`m ≤ n` (`C^t m = n`, `C^ℓ m = m`) with `m ≤ 2^171 ℓ^59`. -/
theorem C_cycle_min_le_poly59 (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) :
    ∃ m, m % 2 = 1 ∧ m ≤ n ∧ (∃ t, C^[t] m = n) ∧ C^[ℓ] m = m ∧ m ≤ 2^171 * ℓ^59 := by
  obtain ⟨m, -, hodd, hmℓ, hmin, hmn, t, ht⟩ := exists_min_odd_T_cycle_aux' n hn ℓ hℓ h
  obtain ⟨j, hj0, hjℓ, -, hT⟩ := exists_T_lap_of_C_cycle hodd hℓ hmℓ
  refine ⟨m, hodd, hmn, ⟨t, ht⟩, hmℓ, ?_⟩
  calc m ≤ 2^171 * j^59 := min_le_poly_period59 hodd hmin hj0 hT
    _ ≤ 2^171 * ℓ^59 := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hjℓ _)

/-- A cycle minimum `n ∈ CycleMinima` with `C^ℓ n = n`, `ℓ > 0` satisfies `n ≤ 2^171 ℓ^59`. -/
theorem cycleMinima_le_poly59 {n ℓ : ℕ} (hmem : n ∈ CycleMinima) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) :
    n ≤ 2^171 * ℓ^59 := by
  obtain ⟨⟨hn, -⟩, hminC⟩ := hmem
  obtain ⟨m, -, hmn, ⟨t, ht⟩, hmℓ, hb⟩ := C_cycle_min_le_poly59 n hn ℓ hℓ h
  have per : C^[ℓ * t] m = m :=
    (Function.IsPeriodicPt.mul_const (show Function.IsPeriodicPt C ℓ m from hmℓ) t).eq
  have hle : t ≤ ℓ * t := Nat.le_mul_of_pos_left t hℓ
  have hback : C^[ℓ * t - t] n = m := by
    rw [← ht, ← Function.iterate_add_apply, Nat.sub_add_cancel hle, per]
  have hnm : n ≤ m := by have := hminC (ℓ * t - t); rwa [hback] at this
  omega

/-! ### Counting cycles of bounded length -/

/-- Cycle minima having some `C`-period `ℓ ∈ (0, N]` lie in `[0, 2^171 N^59]`. -/
theorem cycleMinima_len_le_subset59 (N : ℕ) :
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n} ⊆ Set.Iic (2^171 * N^59) := by
  rintro n ⟨hmem, ℓ, hℓ, hℓN, h⟩
  exact le_trans (cycleMinima_le_poly59 hmem hℓ h)
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hℓN _))

/-- Both conclusions at once; see `finite_cycleMinima_len_le59` and
`ncard_cycleMinima_len_le59`. -/
private theorem finite_cycleMinima_len_le59_aux (N : ℕ) :
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.Finite ∧
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.ncard ≤ 2^171 * N^59 + 1 := by
  refine ⟨(Set.finite_Iic _).subset (cycleMinima_len_le_subset59 N), ?_⟩
  calc _ ≤ (Set.Iic (2^171 * N^59)).ncard :=
        Set.ncard_le_ncard (cycleMinima_len_le_subset59 N) (Set.finite_Iic _)
    _ = 2^171 * N^59 + 1 := ncard_Iic_nat _

/-- The set of cycle minima having a `C`-period `ℓ ∈ (0, N]` is finite. -/
theorem finite_cycleMinima_len_le59 (N : ℕ) :
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.Finite :=
  (finite_cycleMinima_len_le59_aux N).1

/-- At most `2^171 N^59 + 1` cycle minima have a `C`-period `ℓ ∈ (0, N]`; compare the trivial
bound `2^(N+1)`. -/
theorem ncard_cycleMinima_len_le59 (N : ℕ) :
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.ncard ≤ 2^171 * N^59 + 1 :=
  (finite_cycleMinima_len_le59_aux N).2

/-- Cycle minima with minimal `T`-period `≤ N` lie in `[0, 2^171 N^59]`. -/
theorem cycleMinima_minimalPeriod_le_subset59 (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N} ⊆ Set.Iic (2^171 * N^59) := by
  rintro n ⟨hmem, hN⟩
  obtain ⟨hodd, hmin, L, hL, hc⟩ := cycleMinima_T_props hmem
  have hpos : 0 < Function.minimalPeriod T n :=
    Function.minimalPeriod_pos_of_mem_periodicPts ⟨L, hL, hc⟩
  have := min_le_poly_period59 hodd hmin hpos (Function.iterate_minimalPeriod (f := T) (x := n))
  exact le_trans this (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN _))

/-- Both conclusions at once; see `finite_cycleMinima_minimalPeriod_le59` and
`ncard_cycleMinima_minimalPeriod_le59`. -/
private theorem finite_cycleMinima_minimalPeriod_le59_aux (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.Finite ∧
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.ncard ≤ 2^171 * N^59 + 1 := by
  refine ⟨(Set.finite_Iic _).subset (cycleMinima_minimalPeriod_le_subset59 N), ?_⟩
  calc _ ≤ (Set.Iic (2^171 * N^59)).ncard :=
        Set.ncard_le_ncard (cycleMinima_minimalPeriod_le_subset59 N) (Set.finite_Iic _)
    _ = 2^171 * N^59 + 1 := ncard_Iic_nat _

/-- The set of cycle minima with minimal `T`-period at most `N` is finite. -/
theorem finite_cycleMinima_minimalPeriod_le59 (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.Finite :=
  (finite_cycleMinima_minimalPeriod_le59_aux N).1

/-- At most `2^171 N^59 + 1` cycle minima have minimal `T`-period at most `N`. -/
theorem ncard_cycleMinima_minimalPeriod_le59 (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.ncard ≤ 2^171 * N^59 + 1 :=
  (finite_cycleMinima_minimalPeriod_le59_aux N).2

end Collatz
