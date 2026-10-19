/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import FiniteRuns
import Collatz.Diophantine
import CRuns
import Mathlib.Tactic

/-!
# The minimum of a Collatz cycle is polynomial in its length

In this file we prove that the minimum `m` of a nontrivial `T`-cycle of length `L` satisfies
`m ≤ 2^171 L^342`. The ingredients are Crandall's bound `3m (2^L - 3^k) ≤ k 2^L` for the minimum
of a cycle with `k` odd steps, and an effective lower bound
`2^L ≤ 2^172 k^341 (2^L - 3^k)` valid for every `k`, obtained from the gap estimate
`gapBelow_K1big` for `k < 2^100` and the Padé irrationality measure `linFormHyp_uncond` for
`k ≥ 2^100`. As a consequence, there are at most `2^171 N^342 + 1` cycles with a period at
most `N`.

This does not bound the number of cycles, since the bound grows with the length. The exponent is
lowered to `59` in `CycleLenPoly59`.

## Main results

- `gap_all`: if `0 < k` and `3^k < 2^L`, then `2^L ≤ 2^172 k^341 (2^L - 3^k)`.
- `three_min_le_of_cycle`: `3m (2^L - 3^k) ≤ k 2^L` for the minimum `m` of a `T`-cycle.
- `min_le_poly_period`: the odd minimum `m` of a `T`-cycle of length `L > 0` satisfies
  `m ≤ 2^171 L^342`.
- `exists_T_lap_of_C_cycle`: an odd `C`-periodic point `m` with `C^ℓ m = m` returns to itself
  after `j ≤ ℓ` steps of `T`, with `j + S_j(m) = ℓ`.
- `C_cycle_min_le_poly`, `cycleMinima_le_poly`: the same bound for `C`-cycles of length `ℓ`.
- `finite_cycleMinima_len_le`, `ncard_cycleMinima_len_le`: the cycles having a `C`-period at
  most `N` are finite in number, at most `2^171 N^342 + 1`.
- `finite_cycleMinima_minimalPeriod_le`, `ncard_cycleMinima_minimalPeriod_le`: the same for
  minimal `T`-period at most `N`.

## References

- R. E. Crandall, *On the "3x+1" problem*, Math. Comp. 32 (1978), 1281–1292.
- S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math.
  118 (1993), 45–56.
- G. Rhin, *Approximants de Padé et mesures effectives d'irrationalité*, Séminaire de Théorie des
  Nombres, Paris 1985–86, Progr. Math. 71, Birkhäuser (1987), 155–164.
-/

namespace Collatz
open CollatzProof

/-! ### The minimum of a `T`-cycle -/

/-- Effective gap for all `k`: if `0 < k` and `3^k < 2^L`, then `2^L ≤ 2^172 k^341 (2^L − 3^k)`.
For `k < 2^100` this follows from `gapBelow_K1big`, and for `k ≥ 2^100` from `linFormHyp_uncond`. -/
theorem gap_all {k L : ℕ} (hk : 0 < k) (h3 : 3^k < 2^L) :
    2^L ≤ 2^172 * k^341 * (2^L - 3^k) := by
  have hk1 : 1 ≤ k^341 := Nat.one_le_pow _ _ hk
  rcases lt_or_ge k (2^100) with hlt | hge
  · have hK : k < K1big := lt_of_lt_of_le hlt (by norm_num [K1big])
    have := gapBelow_K1big k L hk hK h3
    calc 2^L ≤ 2^170 * (2^L - 3^k) := this
      _ ≤ 2^172 * k^341 * (2^L - 3^k) := by
        apply Nat.mul_le_mul_right
        calc 2^170 = 2^170 * 1 := by ring
          _ ≤ 2^172 * k^341 := Nat.mul_le_mul (by norm_num) hk1
  · have := linFormHyp_uncond k L hge h3
    calc 2^L ≤ 2^2 * k^341 * (2^L - 3^k) := this
      _ ≤ 2^172 * k^341 * (2^L - 3^k) := by
        apply Nat.mul_le_mul_right; apply Nat.mul_le_mul_right; norm_num

/-- Crandall's minimum bound (with subtraction in `ℕ`): for the minimum `m > 0` of a
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

/-- The minimum of a `T`-cycle is polynomial in its length: if `m` is odd and minimal on its
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

/-! ### The minimum of a `C`-cycle -/

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

/-- A positive `C`-cycle of length `ℓ > 0` through `n` contains an odd point
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
  have per : C^[ℓ * t] m = m :=
    (Function.IsPeriodicPt.mul_const (show Function.IsPeriodicPt C ℓ m from hmℓ) t).eq
  have hle : t ≤ ℓ * t := Nat.le_mul_of_pos_left t hℓ
  have hback : C^[ℓ * t - t] n = m := by
    rw [← ht, ← Function.iterate_add_apply, Nat.sub_add_cancel hle, per]
  have hnm : n ≤ m := by have := hminC (ℓ * t - t); rwa [hback] at this
  omega

/-! ### Counting cycles of bounded length -/

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

/-- Both conclusions at once; see `finite_cycleMinima_len_le` and `ncard_cycleMinima_len_le`. -/
private theorem finite_cycleMinima_len_le_aux (N : ℕ) :
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.Finite ∧
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.ncard ≤ 2^171 * N^342 + 1 := by
  refine ⟨(Set.finite_Iic _).subset (cycleMinima_len_le_subset N), ?_⟩
  calc _ ≤ (Set.Iic (2^171 * N^342)).ncard :=
        Set.ncard_le_ncard (cycleMinima_len_le_subset N) (Set.finite_Iic _)
    _ = 2^171 * N^342 + 1 := ncard_Iic_nat _

/-- The set of cycle minima having a `C`-period `ℓ ∈ (0, N]` is finite. -/
theorem finite_cycleMinima_len_le (N : ℕ) :
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.Finite :=
  (finite_cycleMinima_len_le_aux N).1

/-- At most `2^171 N^342 + 1` cycle minima have a `C`-period `ℓ ∈ (0, N]`; compare the trivial
bound `2^(N+1)`. -/
theorem ncard_cycleMinima_len_le (N : ℕ) :
    {n | n ∈ CycleMinima ∧ ∃ ℓ, 0 < ℓ ∧ ℓ ≤ N ∧ C^[ℓ] n = n}.ncard ≤ 2^171 * N^342 + 1 :=
  (finite_cycleMinima_len_le_aux N).2

/-- Cycle minima with minimal `T`-period `≤ N` lie in `[0, 2^171 N^342]`. -/
theorem cycleMinima_minimalPeriod_le_subset (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N} ⊆ Set.Iic (2^171 * N^342) := by
  rintro n ⟨hmem, hN⟩
  obtain ⟨hodd, hmin, L, hL, hc⟩ := cycleMinima_T_props hmem
  have hpos : 0 < Function.minimalPeriod T n :=
    Function.minimalPeriod_pos_of_mem_periodicPts ⟨L, hL, hc⟩
  have := min_le_poly_period hodd hmin hpos (Function.iterate_minimalPeriod (f := T) (x := n))
  exact le_trans this (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hN _))

/-- Both conclusions at once; see `finite_cycleMinima_minimalPeriod_le` and
`ncard_cycleMinima_minimalPeriod_le`. -/
private theorem finite_cycleMinima_minimalPeriod_le_aux (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.Finite ∧
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.ncard ≤ 2^171 * N^342 + 1 := by
  refine ⟨(Set.finite_Iic _).subset (cycleMinima_minimalPeriod_le_subset N), ?_⟩
  calc _ ≤ (Set.Iic (2^171 * N^342)).ncard :=
        Set.ncard_le_ncard (cycleMinima_minimalPeriod_le_subset N) (Set.finite_Iic _)
    _ = 2^171 * N^342 + 1 := ncard_Iic_nat _

/-- The set of cycle minima with minimal `T`-period at most `N` is finite. -/
theorem finite_cycleMinima_minimalPeriod_le (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.Finite :=
  (finite_cycleMinima_minimalPeriod_le_aux N).1

/-- At most `2^171 N^342 + 1` cycle minima have minimal `T`-period at most `N`. -/
theorem ncard_cycleMinima_minimalPeriod_le (N : ℕ) :
    {n | n ∈ CycleMinima ∧ Function.minimalPeriod T n ≤ N}.ncard ≤ 2^171 * N^342 + 1 :=
  (finite_cycleMinima_minimalPeriod_le_aux N).2

end Collatz
