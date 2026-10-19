/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import CycleWord
import Collatz.CycleBasic
import Sieve24

/-!
# Verified ranges of the Collatz conjecture

In this file we define the proposition `VerifiedRangeHyp X0`: every `n` with `0 < n < X0` reaches
`1` under `C`. It is a definition, not an axiom. We prove the instance `X0 = 2^24` from the
kernel-checked descent sieve `descRange_24`, and show that a verified range bounds every odd point
of a nontrivial `T`-cycle from below.

Larger instances (`2^68`, `2^71`) are known only from computer searches in the literature and are
not formalized here. Theorems in other files that take `VerifiedRangeHyp X0` as a hypothesis
are conditional on it.

## Main definitions

- `VerifiedRangeHyp X0`: every `n` with `0 < n < X0` reaches `1` under `C`.

## Main results

- `cycle_mem_of_reaches_one`: a `C`-periodic point that reaches `1` is `1`, `2` or `4`.
- `verifiedRange_mono`: `VerifiedRangeHyp Y` implies `VerifiedRangeHyp X` for `X ≤ Y`.
- `le_of_verifiedRange`: under `VerifiedRangeHyp X0`, every odd `m > 1` on a `T`-cycle satisfies
  `X0 ≤ m`.
- `verifiedRange_of_descRange`: verified descent on `[2, X)` gives `VerifiedRangeHyp X`.
- `verifiedRange_24`: `VerifiedRangeHyp (2^24)`.

## References

- T. Oliveira e Silva, *Empirical verification of the 3x+1 and related conjectures*, in
  J. C. Lagarias (ed.), *The Ultimate Challenge: The 3x+1 Problem*, Amer. Math. Soc. (2010),
  189–207.
- D. Bařina, *Convergence verification of the Collatz problem*, J. Supercomput. 77 (2021),
  2681–2688.
- D. Bařina, *Improved verification limit for the convergence of the Collatz conjecture*,
  J. Supercomput. 81 (2025), Art. 810.
-/

namespace Collatz
open CollatzProof

/-! ### The verified-range hypothesis -/

/-- Every `n` with `0 < n < X0` reaches `1` under `C`. This is a hypothesis, proved in this
library only for `X0 = 2^24` (`verifiedRange_24`); computer searches reach `2^68`
(Bařina 2021) and `2^71` (Bařina 2025). -/
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

/-- A verified range `Y` gives every smaller range `X ≤ Y`. -/
theorem verifiedRange_mono {X Y : ℕ} (hXY : X ≤ Y) (H : VerifiedRangeHyp Y) :
    VerifiedRangeHyp X :=
  fun n hn hnX ↦ H n hn (lt_of_lt_of_le hnX hXY)

/-- Under `VerifiedRangeHyp X0`, every odd `m > 1` lying on a `T`-cycle satisfies `X0 ≤ m`. -/
theorem le_of_verifiedRange {X0 m L : ℕ} (H : VerifiedRangeHyp X0) (hm : 1 < m)
    (hodd : m % 2 = 1) (hL : 0 < L) (hc : T^[L] m = m) : X0 ≤ m := by
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨j, hj⟩ := H m (by omega) hlt
  obtain ⟨ℓ, hℓ, hC⟩ := C_cycle_of_T_cycle hL hc
  rcases cycle_mem_of_reaches_one hℓ hC hj with h | h | h <;> omega

/-! ### Verified ranges from descent -/

/-- Verified descent on `[2, X)` gives the verified range `X`. -/
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

/-- Every `n` with `0 < n < 2^24` reaches `1` under `C`. -/
theorem verifiedRange_24 : VerifiedRangeHyp (2^24) := verifiedRange_of_descRange descRange_24

/-! ### Examples -/

-- The verified range `2^24` bounds every odd point `m > 1` of a `T`-cycle from below.
example {m L : ℕ} (hm : 1 < m) (hodd : m % 2 = 1) (hL : 0 < L) (hc : T^[L] m = m) :
    2^24 ≤ m :=
  le_of_verifiedRange verifiedRange_24 hm hodd hL hc

end Collatz
