/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import Sieve29
import FareyBridge
import PublishedBounds
import VerifiedRange
import Merge

/-!
# Crandall's lower bound on the number of odd elements of a cycle

Crandall proved that a nontrivial `3x + 1` cycle has more than `17985` odd elements. This file
proves a stronger bound by Eliahou's Farey method. The verified range `DescRange 2 (2^20 · 280)`
of `Sieve29` shows that the odd minimum `m` of a nontrivial cycle satisfies
`m ≥ M = 293601280`, so the Farey pair
`50508/31867 < log₂ 3 < log₂ (3 + 1/M) < 24727/15601` (with `24727 · 31867 = 50508 · 15601 + 1`)
applies. By the Farey decomposition `cycle_farey_decomp`, the number of odd elements per lap is
`k = 31867a + 15601b` and the `T`-length is `L = 50508a + 24727b` with `a, b ≥ 1`. Hence
`k ≥ 47468`, `L ≥ 75235`, and the `C`-period is `ℓ = L + k ≥ 122703`.

On a `T`-cycle through its odd minimum `m`, `oddSteps L m` over one lap `T^[L] m = m` counts the
odd elements of the lap, which is Crandall's `k`. In `C`-form, `k ≥ 17986` gives
`ℓ ≥ 17986 + ⌈17986 log₂ 3⌉ = 46494`.

## Main results

- `cycle_farey29`: the Farey decomposition of `(k, L)` at `M = 293601280`.
- `cycle_odd_steps_ge_47468`, `cycle_length_ge_75235`: a nontrivial `T`-cycle has at least
  `47468` odd elements and length at least `75235`.
- `crandall_1978`: Crandall's bound `17985 < oddSteps L m`.
- `cycleLengthAtLeast_122703`, `cycleLengthAtLeast_crandall`: every nontrivial positive `C`-cycle
  has period at least `122703`, and in particular at least `46494`.
- `cycleMinAbove_29`: every positive `C`-periodic point outside `{1, 2, 4}` is at least
  `293601280`.
- `cycle_localmin_ge_29`: the merge lemma of Hercher at `X₀ = 293601280`.

## References

- R. E. Crandall, *On the "3x+1" problem*, Math. Comp. 32 (1978), 1281–1292.
- S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math.
  118 (1993), 45–56.
- C. Hercher, *There are no Collatz m-cycles with m ≤ 91*, J. Integer Seq. 26 (2023),
  Article 23.3.5.
-/

namespace Collatz

open CollatzProof

/-! ### Odd elements and length of a `T`-cycle -/

/-- **Farey decomposition at `M = 293601280`.** If `m > 1` is minimal on its `T`-orbit and
`T^[L] m = m` with `L > 0`, then `oddSteps L m = 31867a + 15601b` and `L = 50508a + 24727b` for
some `a, b ≥ 1`. -/
theorem cycle_farey29 {m L : ℕ} (hm : 1 < m) (hL : 0 < L) (h : T^[L] m = m)
    (hmin : ∀ j, m ≤ T^[j] m) :
    ∃ a b, 0 < a ∧ 0 < b ∧ oddSteps L m = a*31867 + b*15601 ∧ L = a*50508 + b*24727 :=
  cycle_farey_decomp (M := 2^20*280) (by norm_num) (min_orbit_ge_29 hm hmin) hL h hmin
    farey29_det farey29_low farey29_up

/-- Both conclusions of `cycle_odd_steps_ge_47468` and `cycle_length_ge_75235` at once. -/
private theorem cycle_odd_steps_ge_47468_aux {m L : ℕ} (hm : 1 < m) (hL : 0 < L)
    (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m) : 47468 ≤ oddSteps L m ∧ 75235 ≤ L := by
  obtain ⟨a, b, ha, hb, hk, hL'⟩ := cycle_farey29 hm hL h hmin
  constructor <;> omega

/-- **Odd-element bound.** Every nontrivial `T`-cycle, read from its minimum `m > 1` over any
lap `T^[L] m = m` with `L > 0`, has at least `47468` odd elements. -/
theorem cycle_odd_steps_ge_47468 {m L : ℕ} (hm : 1 < m) (hL : 0 < L) (h : T^[L] m = m)
    (hmin : ∀ j, m ≤ T^[j] m) : 47468 ≤ oddSteps L m :=
  (cycle_odd_steps_ge_47468_aux hm hL h hmin).1

/-- Every nontrivial `T`-cycle, read from its minimum `m > 1` over any lap `T^[L] m = m` with
`L > 0`, has length `L ≥ 75235`. -/
theorem cycle_length_ge_75235 {m L : ℕ} (hm : 1 < m) (hL : 0 < L) (h : T^[L] m = m)
    (hmin : ∀ j, m ≤ T^[j] m) : 75235 ≤ L :=
  (cycle_odd_steps_ge_47468_aux hm hL h hmin).2

/-- **Crandall's bound.** An odd `m > 1`, minimal on its `T`-orbit, with `T^[L] m = m`
(`L > 0`), has more than `17985` odd elements per lap: `17985 < oddSteps L m`. -/
theorem crandall_1978 {m L : ℕ} (hm : 1 < m) (_hodd : m % 2 = 1) (hL : 0 < L)
    (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m) : 17985 < oddSteps L m := by
  have := cycle_odd_steps_ge_47468 hm hL h hmin
  omega

/-! ### Cycle lengths and cycle minima under `C` -/

/-- `CycleLengthAtLeast` is antitone in the bound. -/
theorem cycleLengthAtLeast_mono {L L' : ℕ} (h : L' ≤ L) :
    CycleLengthAtLeast L → CycleLengthAtLeast L' :=
  fun H n ℓ hn hℓ hc h1 h2 h4 => le_trans h (H n ℓ hn hℓ hc h1 h2 h4)

/-- **`CycleLengthAtLeast 122703`.** Every nontrivial positive `C`-cycle has period
`ℓ ≥ 122703 = (50508 + 24727) + (31867 + 15601)`. -/
theorem cycleLengthAtLeast_122703 : CycleLengthAtLeast 122703 :=
  cycleLengthAtLeast_122703_of_min29 min_orbit_ge_29

/-- **Crandall's bound in `C`-form.** Every nontrivial positive `C`-cycle has period at least
`46494 = 17986 + 28508`, where `28508 = ⌈17986 log₂ 3⌉`. -/
theorem cycleLengthAtLeast_crandall : CycleLengthAtLeast 46494 :=
  cycleLengthAtLeast_mono (by norm_num) cycleLengthAtLeast_122703

/-- Every `n` with `0 < n < 293601280` reaches `1` under `C`. -/
theorem reach_one_29 : ∀ n, 0 < n → n < 293601280 → ∃ j, C^[j] n = 1 := fun n h1 h2 =>
  reach_one_of_descRange descRange_29 n h1 (by norm_num; omega)

/-- Every positive `C`-periodic `n ∉ {1,2,4}` satisfies
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

/-! ### Instances at `X₀ = 293601280` -/

/-- The verified-range hypothesis holds at `293601280`. -/
theorem verifiedRange_29 : VerifiedRangeHyp (2^20 * 280) :=
  verifiedRange_of_descRange descRange_29

/-- **Merge lemma at `X₀ = 293601280`** (Hercher, Lemma 9). A cycle point `x` followed by an odd
run of exactly `k ≥ 1` steps and then at least two even steps satisfies
`x ≥ 2 · 293601280 + 1`. -/
theorem cycle_localmin_ge_29 {x L k b : ℕ} (hL : 0 < L) (hc : T^[L] x = x) (hk : 1 ≤ k)
    (hb : b % 2 = 1) (hn : x + 1 = 2^k * b) (h4 : (3^k * b) % 4 = 1) :
    2 * 293601280 + 1 ≤ x := by
  have := cycle_localmin_ge (X0 := 2^20*280) (fun m h1 h2 => min_orbit_ge_29 h1 h2)
    hL hc hk hb hn h4
  norm_num at this ⊢; omega

end Collatz
