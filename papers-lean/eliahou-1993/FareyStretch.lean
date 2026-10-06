import Farey

/-!
# Larger Farey instance: `K1 = 225644606` (stretch)

Same machinery as `Farey.lean`, with the Farey pair
`272500658/171928773 > log₂3 > 85137581/53715833` (determinant `1`; the upper fraction is a
convergent, the lower one a convergent as well).  Kernel certificates (`decide +kernel`) are
stated with powers split as `b^(n·a + r) = (replicate n (b^a)).prod · b^r` (`pow_split`), since
the kernel refuses a single `Nat.pow` whose result is too large (≳ 2^24 bits).  The biggest
numbers have about 3.6·10^8 bits; the whole file checks in a couple of minutes.

* `gapBelow_225644606 : GapBelow 225644606 30` (**proved**).
* `few_runs_cycle_trivial_farey2`: **unconditional**, no nontrivial positive `T`-cycle (any
  phase, any period) with `≤ 2` odd runs and `S_L < 225644606`; such a cycle needs
  `L ≥ 357638240`.
* `*_of_linForm_tail2`: **CONDITIONAL** on `LinFormHyp 225644606 c μ` (only `k ≥ 225644606`).

Classical continued-fraction reduction (Eliahou 1993; Simons–de Weger); a finite
instance of Steiner/Simons.
-/

namespace Collatz
open CollatzProof

/-- Splitting a power into a product of `n` equal pieces times a remainder. -/
theorem pow_split (b n a r : ℕ) : b^(n*a + r) = (List.replicate n (b^a)).prod * b^r := by
  rw [List.prod_replicate, pow_add, ← pow_mul, mul_comm n a]

theorem cert2_det : 272500658 * 53715833 = 85137581 * 171928773 + 1 := by norm_num
theorem cert2_above_split : ((List.replicate 40 (3^4298219)).prod * 3^13) < ((List.replicate 40 (2^6812516)).prod * 2^18) := by decide +kernel
theorem cert2_gap_split : ((List.replicate 40 (2^6812516)).prod * 2^18) ≤ 2^30 * (((List.replicate 40 (2^6812516)).prod * 2^18) - ((List.replicate 40 (3^4298219)).prod * 3^13)) := by decide +kernel
theorem cert2_below_split : ((List.replicate 16 (2^5321098)).prod * 2^13) < ((List.replicate 16 (3^3357239)).prod * 3^9) := by decide +kernel
theorem cert2_period_split : ((List.replicate 48 (2^7450796)).prod * 2^31) < ((List.replicate 48 (3^4700929)).prod * 3^14) := by decide +kernel

/-- `3^171928773 < 2^272500658`. -/
theorem cert2_above : 3^171928773 < 2^272500658 := by
  rw [show 171928773 = 40 * 4298219 + 13 from rfl, show 272500658 = 40 * 6812516 + 18 from rfl,
    pow_split, pow_split]; exact cert2_above_split
/-- `2^272500658 ≤ 2^30 (2^272500658 − 3^171928773)`. -/
theorem cert2_gap : 2^272500658 ≤ 2^30 * (2^272500658 - 3^171928773) := by
  rw [show 171928773 = 40 * 4298219 + 13 from rfl, show 272500658 = 40 * 6812516 + 18 from rfl,
    pow_split, pow_split]; exact cert2_gap_split
/-- `2^85137581 < 3^53715833`. -/
theorem cert2_below : 2^85137581 < 3^53715833 := by
  rw [show 53715833 = 16 * 3357239 + 9 from rfl, show 85137581 = 16 * 5321098 + 13 from rfl,
    pow_split, pow_split]; exact cert2_below_split
/-- `2^357638239 < 3^225644606`. -/
theorem cert2_period : 2^357638239 < 3^225644606 := by
  rw [show 357638239 = 48 * 7450796 + 31 from rfl, show 225644606 = 48 * 4700929 + 14 from rfl,
    pow_split, pow_split]; exact cert2_period_split

/-- **Proved:** `GapBelow 225644606 30`. -/
theorem gapBelow_225644606 : GapBelow 225644606 30 :=
  gapBelow_of_farey cert2_det cert2_above cert2_below cert2_gap

/-- **Unconditional, rotation-free.** A positive `T`-cycle point `x` (any phase; `L` any period
`> 0`) whose window has `≤ 2` odd runs and `S_L(x) < 225644606` is `1` or `2`. -/
theorem few_runs_cycle_trivial_farey2 {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (hr : oddRuns L x ≤ 2) (hk : oddSteps L x < 225644606) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_gap gapBelow_225644606 hx hL hc hr hk

/-- Every 1-circuit with `k < 225644606` has `m = 1`; every 2-circuit with
`k1 + k2 < 225644606` has `m = 1`. -/
theorem circuits_eq_one_farey2 :
    (∀ m k l, IsOneCircuit m k l → k < 225644606 → m = 1) ∧
      (∀ m k1 l1 k2 l2, IsTwoCircuit m k1 l1 k2 l2 → k1 + k2 < 225644606 → m = 1) :=
  ⟨fun _ _ _ h hk => one_circuit_eq_one_of_gap gapBelow_225644606 h hk,
   fun _ _ _ _ _ h hk => two_circuit_eq_one_of_gap gapBelow_225644606 h hk⟩

/-- **For `C`-cycles, unconditional.** A nontrivial positive `C`-cycle point `n` yields an odd
`T`-cycle point `m`, `2^17 ≤ m ≤ n`, with (`S_L(m) ≥ 225644606` and `L ≥ 357638240`) or `≥ 3`
odd runs (plus the older fields). -/
theorem nontrivial_C_cycle_three_runs_farey2 (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 971 ≤ oddSteps L m ∧
      (10000 ≤ oddSteps L m ∨ 54 ≤ oddRuns L m) ∧
      ((225644606 ≤ oddSteps L m ∧ 357638239 < L) ∨ 3 ≤ oddRuns L m) :=
  nontrivial_C_cycle_three_runs_of_gap gapBelow_225644606 cert2_period n hn ℓ hℓ h h1 h2 h4

/-- `LinFormHyp 225644606 c μ ⇒ LinFormHyp 100000 c μ` for `c ≥ 30` (the range is proved). -/
theorem linFormHyp_of_tail2 {c μ : ℕ} (hc : 30 ≤ c) (H : LinFormHyp 225644606 c μ) :
    LinFormHyp 100000 c μ := linFormHyp_of_tail_gap gapBelow_225644606 hc H

/-- **CONDITIONAL** on `LinFormHyp 225644606 100 14` (unformalized; constants unchecked
against the literature): every positive `T`-cycle point with `≤ 2` odd runs is `1` or `2`. -/
theorem few_runs_cycle_trivial_of_linForm_tail2 (H : LinFormHyp 225644606 100 14) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_linForm_tail_gap gapBelow_225644606 (by norm_num) H hx hL hc hr

/-- **For `C`-cycles, CONDITIONAL** on `LinFormHyp 225644606 100 14`: every nontrivial `C`-cycle
yields a `T`-cycle point `m ≥ 2^17` whose window has at least 3 odd runs. -/
theorem nontrivial_C_cycle_three_runs_of_linForm_tail2 (H : LinFormHyp 225644606 100 14)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 3 ≤ oddRuns L m :=
  nontrivial_C_cycle_three_runs_of_linForm_tail_gap gapBelow_225644606 (by norm_num) H
    n hn ℓ hℓ h h1 h2 h4

end Collatz

#print axioms Collatz.gapBelow_225644606
#print axioms Collatz.few_runs_cycle_trivial_farey2
#print axioms Collatz.circuits_eq_one_farey2
#print axioms Collatz.nontrivial_C_cycle_three_runs_farey2
#print axioms Collatz.linFormHyp_of_tail2
#print axioms Collatz.few_runs_cycle_trivial_of_linForm_tail2
#print axioms Collatz.nontrivial_C_cycle_three_runs_of_linForm_tail2
