import Sieve29
import FareyBridge
import PublishedBounds
import VerifiedRange
import Merge

/-!
# Crandall 1978 formally, strengthened to `k ≥ 47468`, `ℓ ≥ 122703`

With the kernel verified range `DescRange 2 (2^20·280)` (`Sieve29.lean`, `M = 293601280`), the
odd minimum `m ≥ M` of a nontrivial cycle passes the Farey pair
`50508/31867 < log₂3 < log₂(3 + 1/M) < 24727/15601`  (`24727·31867 = 50508·15601 + 1`),
so by the Eliahou (1993) Farey decomposition (`cycle_farey_decomp`, `FareyDecomp`/`Sieve`) the number of odd
elements per lap is `k = 31867a + 15601b` and the `T`-length is `L = 50508a + 24727b` with
`a, b ≥ 1`.  Hence `k ≥ 47468`, `L ≥ 75235`, and the `C`-period is `ℓ = L + k ≥ 122703`.

**Crandall 1978.** R. E. Crandall, "On the `3x+1` problem", Math. Comp. 32 (1978) 1281–1292,
doi 10.1090/S0025-5718-1978-0480321-3, proves that a nontrivial cycle has more than 17985 odd
elements (`k > 17985`; Crandall counts the elements of the odd-only map).  On a `T`-cycle through
its odd minimum `m`, `oddSteps L m` over one lap `T^[L] m = m` counts exactly the odd elements of
the lap, i.e. Crandall's `k`.  `crandall_1978` is that statement, and `cycle_odd_steps_ge_47468`
is stronger.  In `C`-form, `k ≥ 17986` gives `ℓ ≥ 17986 + ⌈17986 log₂ 3⌉ = 46494`
(`cycleLengthAtLeast_crandall`), again implied by `cycleLengthAtLeast_122703`.

**Classification.** Known mathematics (Crandall 1978; Eliahou 1993 method; a routine verified
range).  To our knowledge the first Lean (machine-checked) proof of Crandall's bound.  Far
below Eliahou 1993 (`ℓ ≥ 17 087 915`) and later work.

**`FareyBridge`/`FareyBridge68`:** compiled with standard axioms (all 64 `Sieve29Part` oleans built at `-P 1`, 23513 s
wall in total, 217–768 s per part). The Farey numerics `farey29_*` and the bridge now live in
`FareyBridge.lean`; `cycleLengthAtLeast_122703` is `cycleLengthAtLeast_122703_of_min29 min_orbit_ge_29`.
-/

namespace Collatz
open CollatzProof

-- `farey29_low`, `farey29_up`, `farey29_det` live in `FareyBridge.lean` (`FareyBridge`/`FareyBridge68`), checked sieve-free.

/-- **Farey decomposition at `M = 293601280`.** If `m > 1` is minimal on its `T`-orbit and
`T^[L] m = m` with `L > 0`, then `oddSteps L m = 31867a + 15601b` and `L = 50508a + 24727b` for
some `a, b ≥ 1`. -/
theorem cycle_farey29 {m L : ℕ} (hm : 1 < m) (hL : 0 < L) (h : T^[L] m = m)
    (hmin : ∀ j, m ≤ T^[j] m) :
    ∃ a b, 0 < a ∧ 0 < b ∧ oddSteps L m = a*31867 + b*15601 ∧ L = a*50508 + b*24727 :=
  cycle_farey_decomp (M := 2^20*280) (by norm_num) (min_orbit_ge_29 hm hmin) hL h hmin
    farey29_det farey29_low farey29_up

/-- **Odd-element bound (T-level).** Every nontrivial `T`-cycle, read from its minimum `m > 1`
over any lap `T^[L] m = m`, `L > 0`, has at least `47468` odd elements and length `L ≥ 75235`. -/
theorem cycle_odd_steps_ge_47468 {m L : ℕ} (hm : 1 < m) (hL : 0 < L) (h : T^[L] m = m)
    (hmin : ∀ j, m ≤ T^[j] m) : 47468 ≤ oddSteps L m ∧ 75235 ≤ L := by
  obtain ⟨a, b, ha, hb, hk, hL'⟩ := cycle_farey29 hm hL h hmin
  constructor <;> omega

/-- **Crandall (1978), formally.** An odd `m > 1`, minimal on its `T`-orbit, with `T^[L] m = m`
(`L > 0`), has more than `17985` odd elements per lap: `17985 < oddSteps L m`. -/
theorem crandall_1978 {m L : ℕ} (hm : 1 < m) (_hodd : m % 2 = 1) (hL : 0 < L)
    (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m) : 17985 < oddSteps L m := by
  have := (cycle_odd_steps_ge_47468 hm hL h hmin).1
  omega

/-- `CycleLengthAtLeast` is antitone in the bound. -/
theorem cycleLengthAtLeast_mono {L L' : ℕ} (h : L' ≤ L) :
    CycleLengthAtLeast L → CycleLengthAtLeast L' :=
  fun H n ℓ hn hℓ hc h1 h2 h4 => le_trans h (H n ℓ hn hℓ hc h1 h2 h4)

/-- **`CycleLengthAtLeast 122703`.** Every nontrivial positive `C`-cycle has period
`ℓ ≥ 122703 = (50508 + 24727) + (31867 + 15601)`. -/
theorem cycleLengthAtLeast_122703 : CycleLengthAtLeast 122703 :=
  cycleLengthAtLeast_122703_of_min29 min_orbit_ge_29

/-- **Crandall (1978) in `C`-form: `CycleLengthAtLeast 46494`** (`46494 = 17986 + 28508`,
`28508 = ⌈17986 log₂ 3⌉`). Implied by `cycleLengthAtLeast_122703`. -/
theorem cycleLengthAtLeast_crandall : CycleLengthAtLeast 46494 :=
  cycleLengthAtLeast_mono (by norm_num) cycleLengthAtLeast_122703

/-- **Verified range, `C`-level.** Every `n` with `0 < n < 293601280` reaches `1` under `C`. -/
theorem reach_one_29 : ∀ n, 0 < n → n < 293601280 → ∃ j, C^[j] n = 1 := fun n h1 h2 =>
  reach_one_of_descRange descRange_29 n h1 (by norm_num; omega)

/-- **`CycleMinAbove (293601280 − 1)`.** Every positive `C`-periodic `n ∉ {1,2,4}` satisfies
`n ≥ 293601280`. -/
theorem cycleMinAbove_29 : CycleMinAbove (293601280 - 1) := by
  rintro n ⟨hn, ℓ, hℓ, h⟩ h1 h2 h4
  obtain ⟨m, hm0, -, -, hmin, hmn, t, ht⟩ := exists_min_odd_T_cycle_aux' n hn ℓ hℓ h
  have hm1 : m ≠ 1 := by
    rintro rfl
    rcases iterate_C_one_mem t with e | e | e <;> rw [ht] at e <;> contradiction
  have h29 : 2^20*280 ≤ m := min_orbit_ge_29 (by omega) hmin
  norm_num at h29
  omega

/-! ## T3: routine instantiations at `X0 = 293601280` -/

/-- `VerifiedRangeHyp 293601280` (unconditional; from `descRange_29`). -/
theorem verifiedRange_29 : VerifiedRangeHyp (2^20 * 280) := verifiedRange_of_descRange descRange_29

/-- Merge lemma (`Merge`, Hercher 2023 Lemma 9) at `X0 = 293601280`: a cycle point `x` followed by an
odd run of exactly `k ≥ 1` steps and then at least two even steps satisfies
`x ≥ 2·293601280 + 1`. -/
theorem cycle_localmin_ge_29 {x L k b : ℕ} (hL : 0 < L) (hc : T^[L] x = x) (hk : 1 ≤ k)
    (hb : b % 2 = 1) (hn : x + 1 = 2^k * b) (h4 : (3^k * b) % 4 = 1) :
    2 * 293601280 + 1 ≤ x := by
  have := cycle_localmin_ge (X0 := 2^20*280) (fun m h1 h2 => min_orbit_ge_29 h1 h2)
    hL hc hk hb hn h4
  norm_num at this ⊢; omega

end Collatz

#print axioms Collatz.cycle_farey29
#print axioms Collatz.cycle_odd_steps_ge_47468
#print axioms Collatz.crandall_1978
#print axioms Collatz.cycleLengthAtLeast_122703
#print axioms Collatz.cycleLengthAtLeast_crandall
#print axioms Collatz.reach_one_29
#print axioms Collatz.cycleMinAbove_29
#print axioms Collatz.verifiedRange_29
#print axioms Collatz.cycle_localmin_ge_29
