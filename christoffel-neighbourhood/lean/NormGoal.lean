import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic

/-!
# Main statement: no cycle is one move away from a Christoffel word

Valuation words `w : ℕ → ℕ` of length `r` (entries `w 0, …, w (r-1)`, the 2-adic valuations
`a_j` of the accelerated odd map `n ↦ (3n+1)/2^{a}`), partial sums `A_j = Σ_{i<j} w i`, and the
Böhm–Sontacchi numerator `B = Σ_{j<r} 3^{r-1-j} 2^{A_j}`. A positive cycle with word `w` and
`A = A_r` satisfies `n · (2^A - 3^r) = B`, so `(2^A - 3^r) ∣ B`.

`chr r A` is the lower Christoffel word of slope `A/r`. Knight (2026) excludes it (for `q > 1`);
the main statement excludes every word obtained from it by ONE cyclic adjacent swap or ONE slide
(move one unit of valuation to a cyclic neighbour). Divisibility is rotation-invariant, so
rotations are covered too.

Suggested route (see experiments/NORM_CRITERION.md): with `θ = 2^{1/r}`, `gcd(A,r) = 1`,
`q ∣ B ⇒ q ∣ Res(X^r - 2, P_w)` where `P_w = Σ_j X^{Δ_j}`, `Δ_j = r A_j - A j` (shifted ≥ 0);
`|Res| = ∏_k |P_w(ζ^k θ)| ≈ e^{0.55 r}` for one move, versus `q ≥ 3^r r^{1-μ}`.

DO NOT EDIT THE STATEMENTS BELOW. The theorem is proved by `sorry` until the search closes it.
-/

namespace Collatz.NormGoal

open Finset

/-- Partial sum `A_j = Σ_{i<j} w i`. -/
def psum (w : ℕ → ℕ) (j : ℕ) : ℕ := ∑ i ∈ range j, w i

/-- Böhm–Sontacchi numerator of a valuation word of length `r`. -/
def Bnum (r : ℕ) (w : ℕ → ℕ) : ℕ := ∑ j ∈ range r, 3 ^ (r - 1 - j) * 2 ^ psum w j

/-- Lower Christoffel word of slope `A / r`: `a_j = ⌊(j+1)A/r⌋ - ⌊jA/r⌋`. -/
def chr (r A : ℕ) (j : ℕ) : ℕ := (j + 1) * A / r - j * A / r

/-- Swap the entries at cyclic positions `j` and `j+1 (mod r)`. -/
def cswap (r : ℕ) (w : ℕ → ℕ) (j : ℕ) (i : ℕ) : ℕ :=
  if i = j then w ((j + 1) % r) else if i = (j + 1) % r then w j else w i

/-- Move one unit of valuation from position `j` to position `k` (`k ≠ j`). -/
def slide (w : ℕ → ℕ) (j k : ℕ) (i : ℕ) : ℕ :=
  if i = j then w j - 1 else if i = k then w k + 1 else w i

/-- `v` is obtained from `w` (length `r`) by one cyclic adjacent swap or one slide to a cyclic
neighbour that keeps every valuation `≥ 1`. -/
def OneMove (r : ℕ) (w v : ℕ → ℕ) : Prop :=
  (∃ j < r, v = cswap r w j) ∨
  (∃ j < r, 2 ≤ w j ∧ ∃ k, (k = (j + 1) % r ∨ (k + 1) % r = j) ∧ k < r ∧ k ≠ j ∧ v = slide w j k)

/-- **Main statement.** For coprime `r ≥ 2`, `A` with `2^A - 3^r > 1`, no word one
move away from the Christoffel word `chr r A` satisfies the cycle divisibility
`(2^A - 3^r) ∣ B`. -/
theorem no_cycle_one_move_christoffel (r A : ℕ) (hr : 2 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (v : ℕ → ℕ) (hv : OneMove r (chr r A) v) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  sorry

end Collatz.NormGoal
