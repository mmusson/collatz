import Farey25
import VerifiedRange

/-!
# Parametric Farey bridge `cycleLengthAtLeast_of_farey`

The Eliahou (1993) Farey method, packaged once and for all.  Suppose

* every odd `m > 1` which is minimal on its `T`-orbit and lies on a `T`-cycle satisfies `M ≤ m`
  (a verified range, kernel-checked or hypothetical), and
* `(p,q), (P,Q)` is a Farey-type pair: `P q = p Q + 1`, `2^p < 3^q` (`p/q < log₂ 3`) and
  `(3M+1)^Q < 2^P M^Q` (`log₂(3 + 1/M) < P/Q`).

Then every nontrivial positive `C`-cycle has period `ℓ ≥ p + q + P + Q`
(`cycleLengthAtLeast_of_farey`); at the `T`-level, a lap through the odd minimum has
`oddSteps ≥ q + Q` and length `≥ p + P` (`cycle_counts_of_farey`).  The proof is that of
`cycleLengthAtLeast_36890` (`Sieve25`/`PublishedBounds`) with the constants abstracted: `cycle_farey_decomp` writes
`S_L = a q + b Q`, `L = a p + b P` with `a, b ≥ 1`.

Sanity instances (all sieve-free):
* `cycleLengthAtLeast_36890'`: the bridge re-derives `Sieve25`/`PublishedBounds` at `M = 2^25`;
* `farey29_low`, `farey29_up`, `farey29_det`: the Crandall numerics at exactly
  `M = 2^20·280 = 293601280` (the margin in `farey29_up` is about `7·10⁻⁷`, so it is stated at
  exactly the `M` delivered by the sieve, no slack);
* `cycleLengthAtLeast_122703_of_min29`: conditional on orbit minima being `≥ 2^20·280`.
* `cycleLengthAtLeast_of_verifiedRange`: variant with `hmin` supplied by `VerifiedRangeHyp M`.

Classical mathematics (Eliahou 1993); infrastructure only.
-/

namespace Collatz
open CollatzProof

/-- **T-level Farey bridge.** If `m > 1` is odd, minimal on its `T`-orbit, `T^[L] m = m` with
`L > 0`, the verified-range hypothesis `hmin` holds at level `M > 0`, and `(p,q),(P,Q)` satisfy
`P q = p Q + 1`, `2^p < 3^q`, `(3M+1)^Q < 2^P M^Q`, then `q + Q ≤ oddSteps L m` and
`p + P ≤ L`. -/
theorem cycle_counts_of_farey {M p q P Q m L : ℕ} (hM : 0 < M)
    (hmin : ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m → M ≤ m)
    (hdet : P * q = p * Q + 1) (hlow : 2^p < 3^q) (hup : (3*M+1)^Q < 2^P * M^Q)
    (hm : 1 < m) (hodd : m % 2 = 1) (hL : 0 < L) (h : T^[L] m = m)
    (hminm : ∀ j, m ≤ T^[j] m) : q + Q ≤ oddSteps L m ∧ p + P ≤ L := by
  obtain ⟨a, b, ha, hb, hk, hL'⟩ :=
    cycle_farey_decomp hM (hmin m hm hodd hminm L hL h) hL h hminm hdet hlow hup
  rw [hk, hL']
  constructor <;> nlinarith

/-- **Parametric Farey bridge (`C`-level).** Under the same hypotheses on `M, p, q, P, Q`,
every nontrivial positive `C`-cycle has period `ℓ ≥ p + q + P + Q`. -/
theorem cycleLengthAtLeast_of_farey {M p q P Q : ℕ} (hM : 0 < M)
    (hmin : ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m → M ≤ m)
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

/-- `hmin` from a verified range: `VerifiedRangeHyp M` gives `M ≤ m` for every odd `m > 1` on a
`T`-cycle. -/
theorem hmin_of_verifiedRange {M : ℕ} (H : VerifiedRangeHyp M) :
    ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m → M ≤ m :=
  fun _ hm hodd _ _ hL hc => le_of_verifiedRange H hm hodd hL hc

/-- **Bridge from a verified range.** `VerifiedRangeHyp M` plus Farey data at `M` give
`CycleLengthAtLeast (p + q + P + Q)`. -/
theorem cycleLengthAtLeast_of_verifiedRange {M p q P Q : ℕ} (hM : 0 < M)
    (H : VerifiedRangeHyp M) (hdet : P * q = p * Q + 1) (hlow : 2^p < 3^q)
    (hup : (3*M+1)^Q < 2^P * M^Q) : CycleLengthAtLeast (p + q + P + Q) :=
  cycleLengthAtLeast_of_farey hM (hmin_of_verifiedRange H) hdet hlow hup

/-- `hmin` from the orbit-minimum form (the shape delivered by `min_orbit_ge_of_descRange`). -/
theorem hmin_of_orbitMin {M : ℕ} (h : ∀ {m : ℕ}, 1 < m → (∀ j, m ≤ T^[j] m) → M ≤ m) :
    ∀ m : ℕ, 1 < m → m % 2 = 1 → (∀ j, m ≤ T^[j] m) → ∀ L, 0 < L → T^[L] m = m → M ≤ m :=
  fun _ hm _ hmin _ _ _ => h hm hmin

/-! ## Sanity instances -/

/-- Sanity (a): the bridge re-derives `Sieve25`/`PublishedBounds` `CycleLengthAtLeast 36890` at `M = 2^25`. -/
theorem cycleLengthAtLeast_36890' : CycleLengthAtLeast 36890 :=
  cycleLengthAtLeast_of_farey (M := 2^25) (p := 1054) (q := 665) (P := 21565) (Q := 13606)
    (by norm_num) (hmin_of_orbitMin min_orbit_ge_25) (by norm_num) farey17_low farey25_up

/-- `50508/31867 < log₂ 3` (kernel, `decide +kernel`). -/
theorem farey29_low : 2^50508 < 3^31867 := by decide +kernel

/-- `log₂(3 + 1/M) < 24727/15601` at exactly `M = 2^20·280 = 293601280` (kernel,
`decide +kernel`; margin about `7·10⁻⁷`). -/
theorem farey29_up : (3*(2^20*280)+1)^15601 < 2^24727 * (2^20*280)^15601 := by decide +kernel

/-- The Farey determinant: `24727·31867 = 50508·15601 + 1`. -/
theorem farey29_det : 24727*31867 = 50508*15601+1 := by norm_num

/-- Sanity (c), sieve-free: if every orbit minimum `m > 1` satisfies `2^20·280 ≤ m`, then
`CycleLengthAtLeast 122703` (`122703 = 50508 + 31867 + 24727 + 15601`). -/
theorem cycleLengthAtLeast_122703_of_min29
    (h : ∀ {m : ℕ}, 1 < m → (∀ j, m ≤ T^[j] m) → 2^20*280 ≤ m) : CycleLengthAtLeast 122703 :=
  cycleLengthAtLeast_of_farey (M := 2^20*280) (p := 50508) (q := 31867) (P := 24727) (Q := 15601)
    (by norm_num) (hmin_of_orbitMin h) farey29_det farey29_low farey29_up

end Collatz

#print axioms Collatz.cycle_counts_of_farey
#print axioms Collatz.cycleLengthAtLeast_of_farey
#print axioms Collatz.cycleLengthAtLeast_of_verifiedRange
#print axioms Collatz.cycleLengthAtLeast_36890'
#print axioms Collatz.farey29_low
#print axioms Collatz.farey29_up
#print axioms Collatz.cycleLengthAtLeast_122703_of_min29
