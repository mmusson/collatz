/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import Farey25
import VerifiedRange

/-!
# Cycle lengths from a verified range and a Farey pair

This file packages Eliahou's Farey method once and for all. Suppose that every odd `m > 1` which
is minimal on its `T`-orbit and lies on a `T`-cycle satisfies `M ≤ m`, and that `(p, q)`, `(P, Q)`
is a Farey-type pair: `Pq = pQ + 1`, `2^p < 3^q` (so `p/q < log₂ 3`) and `(3M + 1)^Q < 2^P M^Q`
(so `log₂ (3 + 1/M) < P/Q`). Then every nontrivial positive `C`-cycle has period at least
`p + q + P + Q`, and at the level of `T`, a lap through the odd minimum has at least `q + Q` odd
steps and length at least `p + P`. The proof writes `oddSteps L m = aq + bQ` and `L = ap + bP`
with `a, b ≥ 1` by `cycle_farey_decomp`.

We also record the numerical facts for Crandall's bound at exactly `M = 2^20 · 280 = 293601280`,
the bound delivered by the verified range of `Sieve29`. The margin in `farey29_up` is about
`7 · 10⁻⁷`, so it is stated at exactly this `M`.

## Main results

- `cycle_oddSteps_ge_of_farey`, `cycle_length_ge_of_farey`: the `T`-level bounds
  `q + Q ≤ oddSteps L m` and `p + P ≤ L`.
- `cycleLengthAtLeast_of_farey`: every nontrivial positive `C`-cycle has period at least
  `p + q + P + Q`.
- `cycleLengthAtLeast_of_verifiedRange`: the same with the hypothesis on minima supplied by
  `VerifiedRangeHyp M`.
- `farey29_low`, `farey29_up`, `farey29_det`: the Farey pair `50508/31867`, `24727/15601` at
  `M = 293601280`.
- `cycleLengthAtLeast_122703_of_min29`: if every orbit minimum `m > 1` is at least `293601280`,
  then every nontrivial positive `C`-cycle has period at least `122703`.

## References

- R. E. Crandall, *On the "3x+1" problem*, Math. Comp. 32 (1978), 1281–1292.
- S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math.
  118 (1993), 45–56.
-/

namespace Collatz

open CollatzProof

/-! ### The Farey bridge -/

/-- Both conclusions of `cycle_oddSteps_ge_of_farey` and `cycle_length_ge_of_farey` at once. -/
private theorem cycle_counts_of_farey_aux {M p q P Q m L : ℕ} (hM : 0 < M)
    (hmin : ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m →
      M ≤ m)
    (hdet : P * q = p * Q + 1) (hlow : 2^p < 3^q) (hup : (3*M+1)^Q < 2^P * M^Q)
    (hm : 1 < m) (hodd : m % 2 = 1) (hL : 0 < L) (h : T^[L] m = m)
    (hminm : ∀ j, m ≤ T^[j] m) : q + Q ≤ oddSteps L m ∧ p + P ≤ L := by
  obtain ⟨a, b, ha, hb, hk, hL'⟩ :=
    cycle_farey_decomp hM (hmin m hm hodd hminm L hL h) hL h hminm hdet hlow hup
  rw [hk, hL']
  constructor <;> nlinarith

/-- **Farey bridge for `T`-cycles.** If `m > 1` is odd, minimal on its `T`-orbit, and
`T^[L] m = m` with `L > 0`, the verified-range hypothesis `hmin` holds at level `M > 0`, and
`(p, q), (P, Q)` satisfy `P q = p Q + 1`, `2^p < 3^q` and `(3M + 1)^Q < 2^P M^Q`, then
`q + Q ≤ oddSteps L m`. -/
theorem cycle_oddSteps_ge_of_farey {M p q P Q m L : ℕ} (hM : 0 < M)
    (hmin : ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m →
      M ≤ m)
    (hdet : P * q = p * Q + 1) (hlow : 2^p < 3^q) (hup : (3*M+1)^Q < 2^P * M^Q)
    (hm : 1 < m) (hodd : m % 2 = 1) (hL : 0 < L) (h : T^[L] m = m)
    (hminm : ∀ j, m ≤ T^[j] m) : q + Q ≤ oddSteps L m :=
  (cycle_counts_of_farey_aux hM hmin hdet hlow hup hm hodd hL h hminm).1

/-- Under the hypotheses of `cycle_oddSteps_ge_of_farey`, the cycle length satisfies
`p + P ≤ L`. -/
theorem cycle_length_ge_of_farey {M p q P Q m L : ℕ} (hM : 0 < M)
    (hmin : ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m →
      M ≤ m)
    (hdet : P * q = p * Q + 1) (hlow : 2^p < 3^q) (hup : (3*M+1)^Q < 2^P * M^Q)
    (hm : 1 < m) (hodd : m % 2 = 1) (hL : 0 < L) (h : T^[L] m = m)
    (hminm : ∀ j, m ≤ T^[j] m) : p + P ≤ L :=
  (cycle_counts_of_farey_aux hM hmin hdet hlow hup hm hodd hL h hminm).2

/-- **Farey bridge for `C`-cycles.** Under the same hypotheses on `M, p, q, P, Q`, every
nontrivial positive `C`-cycle has period `ℓ ≥ p + q + P + Q`. -/
theorem cycleLengthAtLeast_of_farey {M p q P Q : ℕ} (hM : 0 < M)
    (hmin : ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m →
      M ≤ m)
    (hdet : P * q = p * Q + 1) (hlow : 2^p < 3^q) (hup : (3*M+1)^Q < 2^P * M^Q) :
    CycleLengthAtLeast (p + q + P + Q) := by
  intro n ℓ hn hℓ h h1 h2 h4
  obtain ⟨m, hm0, hodd, hmℓ, hminm, hmn, t, ht⟩ := exists_min_odd_T_cycle_aux' n hn ℓ hℓ h
  have hm1 : m ≠ 1 := by
    rintro rfl
    rcases iterate_C_one_mem t with e | e | e <;> rw [ht] at e <;> contradiction
  obtain ⟨j, hj0, -, hjk, hT⟩ := exists_T_lap_of_C_cycle hodd hℓ hmℓ
  obtain ⟨a, b, ha, hb, hk, hL⟩ := cycle_farey_decomp hM
    (hmin m (by omega) hodd hminm j hj0 hT) hj0 hT hminm hdet hlow hup
  rw [hk, hL] at hjk
  nlinarith

/-! ### Supplying the hypothesis on minima -/

/-- `VerifiedRangeHyp M` gives `M ≤ m` for every odd `m > 1` on a `T`-cycle. -/
theorem hmin_of_verifiedRange {M : ℕ} (H : VerifiedRangeHyp M) :
    ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m → M ≤ m :=
  fun _ hm hodd _ _ hL hc => le_of_verifiedRange H hm hodd hL hc

/-- `VerifiedRangeHyp M` and Farey data at `M` give `CycleLengthAtLeast (p + q + P + Q)`. -/
theorem cycleLengthAtLeast_of_verifiedRange {M p q P Q : ℕ} (hM : 0 < M)
    (H : VerifiedRangeHyp M) (hdet : P * q = p * Q + 1) (hlow : 2^p < 3^q)
    (hup : (3*M+1)^Q < 2^P * M^Q) : CycleLengthAtLeast (p + q + P + Q) :=
  cycleLengthAtLeast_of_farey hM (hmin_of_verifiedRange H) hdet hlow hup

/-- The hypothesis on minima from the orbit-minimum form delivered by
`min_orbit_ge_of_descRange`. -/
theorem hmin_of_orbitMin {M : ℕ} (h : ∀ {m : ℕ}, 1 < m → (∀ j, m ≤ T^[j] m) → M ≤ m) :
    ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m → M ≤ m :=
  fun _ hm _ hmin _ _ _ => h hm hmin

/-! ### Crandall's numerics at `M = 293601280` -/

/-- `50508/31867 < log₂ 3` (checked by the kernel). -/
theorem farey29_low : 2^50508 < 3^31867 := by decide +kernel

/-- `log₂ (3 + 1/M) < 24727/15601` at exactly `M = 2^20 · 280 = 293601280` (checked by the
kernel; the margin is about `7 · 10⁻⁷`). -/
theorem farey29_up : (3*(2^20*280)+1)^15601 < 2^24727 * (2^20*280)^15601 := by decide +kernel

/-- The Farey determinant: `24727·31867 = 50508·15601 + 1`. -/
theorem farey29_det : 24727*31867 = 50508*15601+1 := by norm_num

/-- If every orbit minimum `m > 1` satisfies `2^20·280 ≤ m`, then
`CycleLengthAtLeast 122703` (`122703 = 50508 + 31867 + 24727 + 15601`). -/
theorem cycleLengthAtLeast_122703_of_min29
    (h : ∀ {m : ℕ}, 1 < m → (∀ j, m ≤ T^[j] m) → 2^20*280 ≤ m) : CycleLengthAtLeast 122703 :=
  cycleLengthAtLeast_of_farey (M := 2^20*280) (p := 50508) (q := 31867) (P := 24727)
    (Q := 15601) (by norm_num) (hmin_of_orbitMin h) farey29_det farey29_low farey29_up

/-! ### Examples -/

-- The bridge recovers `cycleLengthAtLeast_36890` of `Farey25` at `M = 2^25`.
example : CycleLengthAtLeast 36890 :=
  cycleLengthAtLeast_of_farey (M := 2^25) (p := 1054) (q := 665) (P := 21565) (Q := 13606)
    (by norm_num) (hmin_of_orbitMin min_orbit_ge_25) (by norm_num) farey17_low farey25_up

end Collatz
