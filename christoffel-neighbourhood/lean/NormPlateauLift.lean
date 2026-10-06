import NormLebel
import NormCycleAll
import BackCong
import Mathlib.Tactic.NormNum.Prime

/-!
# a single-prime instance of Lebel's Conjecture 11.1 with composite `D`

Notation: `D = q = 2^A - 3^r`, `B(v)` the Böhm–Sontacchi numerator, `chr r A` the Christoffel word.

* `lebel_single_prime_37_19`: at `(A, r) = (37, 19)`, `D = 5 · 27255338401`; `5` is bad
  for a one-move word, while `P^+(D)` divides `B` of no one-move word (via
  `NormLebel.lebel_strong_of_large_prime`).

Credit: Lebel (`christoffel_collatz_v3.tex`, Conj. 11.1); one-move framework: Knight, Lebel,
Solomon.
-/

namespace Collatz.NormPlateauLift
open Collatz.NormGoal Collatz.NormReduce Collatz.NormShift Finset


section Cycle
open CollatzProof

end Cycle


/-! ### T2: a single-prime instance of Lebel's Conjecture 11.1 with composite `D` -/

set_option maxRecDepth 200000 in
/-- `27255338401` is prime (`norm_num` trial division). -/
theorem prime_27255338401 : Nat.Prime 27255338401 := by norm_num

/-- **Lebel Conj. 11.1, strong form, at `(A, r) = (37, 19)`.**
`D = 2^37 - 3^19 = 5 · 27255338401` with `P = 27255338401` prime, so `P = P^+(D)`. The prime `5`
is BAD: it divides `B` of the one-move word `slide (NormGoal.chr 19 37) 4 5` (cf. Lebel's Thm 7.2).
Yet `P` divides `B` of NO one-move neighbour of `NormGoal.chr 19 37` (`NormLebel.lebel_strong_of_large_prime`,
size margin about 600.7 vs 658.7 bits). An instance only; the conjecture stays open. -/
theorem lebel_single_prime_37_19 :
    2 ^ 37 - 3 ^ 19 = 5 * 27255338401 ∧ Nat.Prime 27255338401 ∧
    (∃ v, OneMove 19 (NormGoal.chr 19 37) v ∧ 5 ∣ Bnum 19 v) ∧
    (∀ p, p.Prime → p ∣ 2 ^ 37 - 3 ^ 19 → p ≤ 27255338401) ∧
    ∀ v, OneMove 19 (NormGoal.chr 19 37) v → ¬ 27255338401 ∣ Bnum 19 v := by
  have hD : 2 ^ 37 - 3 ^ 19 = 5 * 27255338401 := by norm_num
  have hmax : ∀ p, p.Prime → p ∣ 2 ^ 37 - 3 ^ 19 → p ≤ 27255338401 := by
    intro p hp hpD
    rw [hD] at hpD
    rcases (Nat.Prime.dvd_mul hp).mp hpD with h | h
    · have := Nat.le_of_dvd (by norm_num) h; omega
    · exact Nat.le_of_dvd (by norm_num) h
  have hPD : 27255338401 ∣ 2 ^ 37 - 3 ^ 19 := by rw [hD]; exact Dvd.intro_left _ rfl
  refine ⟨hD, prime_27255338401, ⟨slide (NormGoal.chr 19 37) 4 5, ?_, by decide +kernel⟩, hmax, ?_⟩
  · exact Or.inr ⟨4, by norm_num, by decide, 5, Or.inl (by norm_num), by norm_num, by norm_num, rfl⟩
  · exact NormLebel.lebel_strong_of_large_prime 19 37 27255338401 27255338401 (by norm_num)
      (by norm_num) (by norm_num) prime_27255338401 hPD (by decide +kernel) hPD hmax

end Collatz.NormPlateauLift

#print axioms Collatz.NormPlateauLift.prime_27255338401
#print axioms Collatz.NormPlateauLift.lebel_single_prime_37_19
