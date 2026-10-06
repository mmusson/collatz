import CollatzSearch.CycleWord
import CollatzSearch.CycleBasic
import CollatzSearch.Sieve24

/-!
# Parametric verified-range interface

`VerifiedRangeHyp X0` says every `n` with `0 < n < X0` reaches `1` under `C`.  It is a
**definition** (a `Prop`), not an axiom.  Unconditionally we prove `VerifiedRangeHyp (2^24)`
from the kernel-certified sieve `descRange_24`.  Larger instances (`2^68`, `2^71`) are known
only from computation in the literature (Oliveira e Silva 2010; Barina 2020, 2025), not
formalized here; theorems taking `VerifiedRangeHyp X0` as a hypothesis are CONDITIONAL on it.

Classical; NOT progress on `no_nontrivial_cycles`.
-/

namespace CollatzSearch
open CollatzProof

/-- CONDITIONAL interface (a def, not an axiom): every `n` with `0 < n < X0` reaches `1`
under `C`.  Literature: Oliveira e Silva 2010 (`2^60`, later `5·2^60`), Barina 2020 (`2^68`),
Barina 2025 (`2^71`).  Only `X0 = 2^24` is proved in this library (`verifiedRange_24`).
Citations (from memory; web search unavailable in `Generalized` and `VerifiedRuns`, so treat as "as quoted in the
literature"): D. Barina, "Convergence verification of the Collatz problem", The Journal of
Supercomputing 77 (2021) 2681–2688 (online 2020), range `2^68`; D. Barina, "Improved
verification limit for the convergence of the Collatz conjecture", The Journal of
Supercomputing (2025), range `2^71` (bibliographic details unconfirmed). -/
def VerifiedRangeHyp (X0 : ℕ) : Prop := ∀ n, 0 < n → n < X0 → ∃ j, C^[j] n = 1

/-- A `C`-periodic point (period `ℓ > 0`) some iterate of which equals `1` is `1`, `2` or `4`. -/
theorem cycle_mem_of_reaches_one {n ℓ j : ℕ} (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hj : C^[j] n = 1) : n = 1 ∨ n = 2 ∨ n = 4 := by
  have hp : Function.IsPeriodicPt C ℓ n := h
  have hpj : C^[ℓ*j] n = n := (hp.mul_const j).eq
  have hle : j ≤ ℓ*j := Nat.le_mul_of_pos_left j hℓ
  have e : ℓ*j = (ℓ*j - j) + j := (Nat.sub_add_cancel hle).symm
  rw [e, Function.iterate_add_apply, hj] at hpj
  rw [← hpj]
  exact iterate_C_one_mem _

/-- Monotonicity of the interface: a verified range `Y` gives every smaller range `X ≤ Y`. -/
theorem verifiedRange_mono {X Y : ℕ} (hXY : X ≤ Y) (H : VerifiedRangeHyp Y) :
    VerifiedRangeHyp X :=
  fun n hn hnX => H n hn (lt_of_lt_of_le hnX hXY)

/-- Under `VerifiedRangeHyp X0`, every odd `m > 1` lying on a `T`-cycle satisfies `X0 ≤ m`
(no minimality needed). -/
theorem le_of_verifiedRange {X0 m L : ℕ} (H : VerifiedRangeHyp X0) (hm : 1 < m)
    (hodd : m % 2 = 1) (hL : 0 < L) (hc : T^[L] m = m) : X0 ≤ m := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨j, hj⟩ := H m (by omega) hlt
  obtain ⟨ℓ, hℓ, hC⟩ := C_cycle_of_T_cycle hL hc
  rcases cycle_mem_of_reaches_one hℓ hC hj with h | h | h <;> omega

/-- Verified descent on `[2, X)` gives the interface at `X`. -/
theorem verifiedRange_of_descRange {X : ℕ} (hD : DescRange 2 X) : VerifiedRangeHyp X := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn hnX
    rcases Nat.lt_or_ge n 2 with h1 | h2
    · exact ⟨0, by simp; omega⟩
    · obtain ⟨j, hj⟩ := hD n h2 hnX
      obtain ⟨i, hi⟩ := exists_iterate_T_eq_iterate_C j n
      rw [hi] at hj
      have hy : 0 < C^[i] n := iterate_C_pos hn i
      obtain ⟨j', hj'⟩ := ih _ hj hy (lt_trans hj hnX)
      exact ⟨j' + i, by rw [Function.iterate_add_apply]; exact hj'⟩

/-- **Unconditional instance.** Every `n` with `0 < n < 2^24` reaches `1` under `C`. -/
theorem verifiedRange_24 : VerifiedRangeHyp (2^24) := verifiedRange_of_descRange descRange_24

/-- Sanity: the interface recovers the `2^24` lower bound for odd cycle points (no minimality). -/
theorem odd_T_cycle_ge_24 {m L : ℕ} (hm : 1 < m) (hodd : m % 2 = 1) (hL : 0 < L)
    (hc : T^[L] m = m) : 2^24 ≤ m :=
  le_of_verifiedRange verifiedRange_24 hm hodd hL hc

end CollatzSearch

#print axioms CollatzSearch.cycle_mem_of_reaches_one
#print axioms CollatzSearch.verifiedRange_mono
#print axioms CollatzSearch.le_of_verifiedRange
#print axioms CollatzSearch.verifiedRange_of_descRange
#print axioms CollatzSearch.verifiedRange_24
#print axioms CollatzSearch.odd_T_cycle_ge_24
