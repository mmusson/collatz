import NormShift
import NormPlateau

/-!
# one-unit slides for every `(r, A)` and every actual `T`-cycle

One unit of valuation slid ANY distance in the Christoffel word, `v = slide (chr r A) a b`
(`a ≠ b < r`, `chr a ≥ 2`), never satisfies the cycle divisibility `(2^A - 3^r) ∣ B(v)` for
`r ≥ 40901`, whatever `gcd(A, r)` is:

* `no_cycle_slide_coprime` (T2): `gcd(A, r) = 1` (not reached by `NormPlateau`'s cofactor method,
  nor by the norm route of `NormTwo`) — via `NormShift.slide_word_coprime`.
* `no_cycle_slide_gcd` / `no_cycle_slide_gcd2` (T3): any `d = gcd ≥ 2` under
  `2^176 r^59 < 3^{⌊(r - r/d)/(d+2)⌋+1}`; for `d = 2` this is automatic (`r ≥ 40901`).
* `no_cycle_slide_allRA`: all `(r, A)` (`gcd ≥ 3` via `NormPlateau` `NormPlateau.no_cycle_slide_noncoprime3`).
* `cycle_slide_all` (T4): no nontrivial positive `T`-cycle has as valuation word (read from the
  chosen start `m`) a slide of `chr r L`, for any `gcd(L, r)` and any distance.
* `no_cycle_few_levels_coprime`, `cycle_few_levels_coprime` (T5): coprime words of height `H₀`
  with `J` cyclic level changes, `2^{2H₀+174} r^59 < 3^{⌊r/(6J+3)⌋+1}` (e.g.
  `J ≤ 9` at `r = 40903`, `H₀ = 1`). T5 is a run-count / level-change variant of Mghirbi's
  support-height criterion (`2s+1` vs `6J+3`, `p^{13.3}` vs `r^59`): it wins for plateaus and
  loses for isolated defects, so it is not a uniform strengthening.

Prior art: Mghirbi (Zenodo 21734655) Thm 1.3 covers height-one interval bridges only for area
`D ≲ 0.038 r / log r`, via his Thm 6.3/6.4/Lemma 7.2 lift (coprime, `t = 1`); `NormMain`:
`D = 1`; `NormPlateau`: `gcd ≥ 3`; Solomon (Zenodo 22220730, Prop. 6.3)
cofactor; Knight, Lebel. Here: every `D`, every `(r, A)`, `r ≥ 40901`.

Scope: word-level / cycle-equation exclusions. Rotations: `cycle_slide_all` reads the
word from the chosen start; start-free forms (any rotation of a slide of `chr r L`) are not
treated here.
-/

namespace Collatz.NormShiftSlide
open Collatz.NormGoal Finset

/-- **T2: one unit slid any distance, coprime case.** For `r ≥ 40901`,
`gcd(A, r) = 1`, `3^r + 1 < 2^A`, and any `a ≠ b < r` with `chr r A a ≥ 2`, the word obtained
from the Christoffel word by moving one unit from position `a` to position `b` does not satisfy
`(2^A - 3^r) ∣ B`. -/
theorem no_cycle_slide_coprime (r A a b : ℕ) (hr : 40901 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (ha : a < r) (hb : b < r) (hab : a ≠ b)
    (h2 : 2 ≤ NormGoal.chr r A a) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r (NormGoal.slide (NormGoal.chr r A) a b) := by
  obtain ⟨hv1, hsum, hps⟩ := NormPlateau.slide_facts hq ha hb hab h2
  exact NormShift.slide_word_coprime (by omega) hcop hq ha hb hv1 hsum hps
    (gap_all59 (by omega) (by omega)) (NormShift.big_r10 hr)

/-- **T3: one unit slid any distance, `gcd(A, r) = d ≥ 2`.** Under
`r/d ≥ 2` and `2^176 r^59 < 3^{⌊(r - r/d)/(d+2)⌋+1}`, no slide of `chr r A` satisfies
`(2^A - 3^r) ∣ B`. No coprimality. -/
theorem no_cycle_slide_gcd (r A a b d : ℕ) (hd2 : 2 ≤ d) (hd : Nat.gcd A r = d)
    (hrd : 2 ≤ r / d) (hq : 3 ^ r + 1 < 2 ^ A)
    (hbig : 2 ^ 176 * r ^ 59 < 3 ^ ((r - r / d) / (d + 2) + 1))
    (ha : a < r) (hb : b < r) (hab : a ≠ b) (h2 : 2 ≤ NormGoal.chr r A a) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r (NormGoal.slide (NormGoal.chr r A) a b) := by
  obtain ⟨hv1, hsum, hps⟩ := NormPlateau.slide_facts hq ha hb hab h2
  have hr0 : 0 < r := by omega
  exact NormShift.slide_word_gcd hd2 hd hrd hq ha hb hv1 hsum hps
    (gap_all59 hr0 (by omega)) hbig

/-- **T3, `d = 2`.** For `r ≥ 40901`, `gcd(A, r) = 2`, every slide of `chr r A`
is excluded. -/
theorem no_cycle_slide_gcd2 (r A a b : ℕ) (hr : 40901 ≤ r) (hd : Nat.gcd A r = 2)
    (hq : 3 ^ r + 1 < 2 ^ A) (ha : a < r) (hb : b < r) (hab : a ≠ b)
    (h2 : 2 ≤ NormGoal.chr r A a) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r (NormGoal.slide (NormGoal.chr r A) a b) := by
  refine no_cycle_slide_gcd r A a b 2 le_rfl hd (by omega) hq ?_ ha hb hab h2
  calc 2 ^ 176 * r ^ 59 < 3 ^ (r / 10 + 1) := NormShift.big_r10 hr
    _ ≤ 3 ^ ((r - r / 2) / (2 + 2) + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

/-- **One-unit slides at word level, all `(r, A)`.** For `r ≥ 40901` and
`3^r + 1 < 2^A` (no hypothesis on `gcd(A, r)`), no word obtained from `chr r A` by moving one
unit from a position `a` (with `chr a ≥ 2`) to any other position `b` satisfies
`(2^A - 3^r) ∣ B`. Cases: `gcd = 1` T2; `gcd = 2` T3; `gcd ≥ 3` `NormPlateau`
(`NormPlateau.no_cycle_slide_noncoprime3`). -/
theorem no_cycle_slide_allRA (r A a b : ℕ) (hr : 40901 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A)
    (ha : a < r) (hb : b < r) (hab : a ≠ b) (h2 : 2 ≤ NormGoal.chr r A a) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r (NormGoal.slide (NormGoal.chr r A) a b) := by
  have hpos : 0 < Nat.gcd A r := Nat.gcd_pos_of_pos_right _ (by omega)
  rcases (show Nat.gcd A r = 1 ∨ Nat.gcd A r = 2 ∨ 3 ≤ Nat.gcd A r by omega) with h1 | h2' | h3
  · exact no_cycle_slide_coprime r A a b hr h1 hq ha hb hab h2
  · exact no_cycle_slide_gcd2 r A a b hr h2' hq ha hb hab h2
  · have hrA := NormReduce.r_lt_A hq
    have h6 : (32 * r) ^ 6 < 2 ^ A := by
      calc (32 * r) ^ 6 = 2 ^ 30 * r ^ 6 := by ring
        _ < 2 ^ r := NormPlateau.pow6 r (by omega)
        _ ≤ 2 ^ A := Nat.pow_le_pow_right (by norm_num) hrA.le
    exact NormPlateau.no_cycle_slide_noncoprime3 r A h3 hq h6 a b ha hb hab h2

section Cycle
open CollatzProof

/-- **T4: one-unit slides for every actual `T`-cycle.** No nontrivial (`m ≠ 1`)
positive `T`-cycle with `r ≥ 2` odd steps and period `L` has as valuation word (read from the
chosen start `m`) a slide of `chr r L` — one unit moved from any position `a` (`chr a ≥ 2`) to
any other position `b`. No hypothesis on `gcd(L, r)` and none on the distance `|a - b|`.
Proof: `NormTwo.cycle_q` (`3^r + 1 < 2^L`, `q ∣ B`), `NormCycleAll.cycle_params` (`r ≥ 40901`),
`no_cycle_slide_allRA`. -/
theorem cycle_slide_all {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hm : m ≠ 1)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (a b : ℕ) (ha : a < r) (hb : b < r) (hab : a ≠ b) (h2 : 2 ≤ NormGoal.chr r L a)
    (hv : ∀ i < r, v i = NormGoal.slide (NormGoal.chr r L) a b i) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  obtain ⟨-, hr4⟩ := NormCycleAll.cycle_params (by omega) hv1 hL hodd hcyc hm
  rw [NormPlateau.Bnum_congr hv] at hdiv
  exact no_cycle_slide_allRA r L a b hr4 hq ha hb hab h2 hdiv

end Cycle

/-- **T5, unconditional word form.** For coprime `(A, r)`, `3^r + 1 < 2^A`, any word
(letters `≥ 1`, `psum v r = A`) whose deviation `ε_j = psum v j - ⌊jA/r⌋` satisfies `|ε| ≤ H₀`
and changes level (cyclically) only at the `J = |P|` points of `P`, with
`2^{2H₀+174} r^59 < 3^{⌊r/(6J+3)⌋+1}`, has `(2^A - 3^r) ∤ B(v)`. So a cycle word of bounded
height must change level at least about `r / (6 log₃(2^{2H₀+174} r^59))` times; e.g. at
`r = 40903`, `H₀ = 1`, every word with at most 9 level changes is excluded.
This is a run-count / level-change variant of Mghirbi's support-height criterion (Zenodo
21734655): his `3^{p/(2s+1)}` vs `2^{14.3}(8s+2)^{2H} p^{13.3}` (in the number `s` of defect
points) against our `3^{r/(6J+3)}` vs `2^{2H₀+174} r^59` (in the number `J` of level changes).
Ours wins for plateau / run-structured deviations (`J ≪ s`) and loses for isolated defects
(`J ≈ 2s`); it is NOT a uniform strengthening. -/
theorem no_cycle_few_levels_coprime {r A H₀ : ℕ} {v : ℕ → ℕ} (hr : 0 < r)
    (hcop : Nat.Coprime A r) (hq : 3 ^ r + 1 < 2 ^ A) (hv1 : ∀ i < r, 1 ≤ v i)
    (hA : psum v r = A) (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, NormShift.eps r A v c ≠ NormShift.eps r A v (NormShift.prv r c) → c ∈ P)
    (hup : ∀ j < r, psum v j ≤ j * A / r + H₀) (hdn : ∀ j < r, j * A / r ≤ psum v j + H₀)
    (hbig : 2 ^ (2 * H₀ + 174) * r ^ 59 < 3 ^ (r / (6 * P.card + 3) + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v :=
  NormShift.few_levels_coprime hr hcop hq hv1 hA P hP hchg hup hdn
    (gap_all59 hr (by omega)) hbig

section Cycle2
open CollatzProof

/-- **T5, cycle form.** No positive `T`-cycle with `r ≥ 2` odd steps, period `L`,
`gcd(L, r) = 1`, has a valuation word whose deviation from `chr r L` is bounded by `H₀` and
changes level only at the points of `P`, when `2^{2H₀+174} r^59 < 3^{⌊r/(6|P|+3)⌋+1}`. -/
theorem cycle_few_levels_coprime {m L r H₀ : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r)
    (hcop : Nat.Coprime L r) (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, NormShift.eps r L v c ≠ NormShift.eps r L v (NormShift.prv r c) → c ∈ P)
    (hup : ∀ j < r, psum v j ≤ j * L / r + H₀) (hdn : ∀ j < r, j * L / r ≤ psum v j + H₀)
    (hbig : 2 ^ (2 * H₀ + 174) * r ^ 59 < 3 ^ (r / (6 * P.card + 3) + 1)) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  exact no_cycle_few_levels_coprime (by omega) hcop hq hv1 hL P hP hchg hup hdn hbig hdiv

end Cycle2

end Collatz.NormShiftSlide

#print axioms Collatz.NormShiftSlide.no_cycle_slide_coprime
#print axioms Collatz.NormShiftSlide.no_cycle_slide_gcd
#print axioms Collatz.NormShiftSlide.no_cycle_slide_gcd2
#print axioms Collatz.NormShiftSlide.no_cycle_slide_allRA
#print axioms Collatz.NormShiftSlide.cycle_slide_all
#print axioms Collatz.NormShiftSlide.no_cycle_few_levels_coprime
#print axioms Collatz.NormShiftSlide.cycle_few_levels_coprime