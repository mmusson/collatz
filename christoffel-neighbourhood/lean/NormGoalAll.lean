import NormGoal

/-!
# Main statement: extend NormGoal to ALL `(r, A)`

`Collatz.NormMain.no_cycle_one_move_christoffel` proves the case `Nat.Coprime A r`.
This file states the extension without coprimality. The hypothesis `v ≠ chr r A` (on `range r`)
is needed: for `A = 2r` the identity "swap" of two equal entries returns `chr r (2r) = (2,…,2)`,
the trivial cycle `n = 1`, which does satisfy the divisibility. Brute force (r < 130, A up to
⌈r log₂3⌉+6, all gcds): 117,492 words, no counterexample (experiments/, 2026-10-04).

Suggested route for `d = gcd(A, r) > 1` (Solomon 2026, Prop. 6.3 — cite it):
`chr r A` is the `d`-fold repetition of `chr (r/d) (A/d)`; with `U = 2^{A/d}`, `V = 3^{r/d}`,
`2^A - 3^r = (U - V) · S_d`, `S_d = Σ_{j<d} U^j V^{d-1-j} > 1`, `gcd(S_d, 6) = 1`, and
`Bnum (repetition) = S_d · Bnum (block)`. A non-wrap one-move changes `Bnum` by one monomial
`± 2^a 3^b` (or `± 2^{a-1} 3^b`); wrap moves reduce to non-wrap moves of a rotation using the
rotation identity `2^{w 0} · Bnum (rot w) = 3 · Bnum w + (2^A - 3^r)` (prove it) and the fact
that rotations of a `d`-periodic word are `d`-periodic.

DO NOT EDIT THE STATEMENT BELOW.
-/

namespace Collatz.NormGoal

/-- **Main statement.** For all `r ≥ 2`, `A` with `2^A - 3^r > 1` (no coprimality),
no word one move away from `chr r A`, other than `chr r A` itself, satisfies
`(2^A - 3^r) ∣ Bnum`. -/
theorem no_cycle_one_move_christoffel_all (r A : ℕ) (hr : 2 ≤ r)
    (hq : 3 ^ r + 1 < 2 ^ A) (v : ℕ → ℕ) (hv : OneMove r (chr r A) v)
    (hne : ∃ j < r, v j ≠ chr r A j) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  sorry

end Collatz.NormGoal
