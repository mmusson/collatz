# Collatz cycles: results and Lean 4 proofs

Lean 4 formalizations of published results on Collatz cycles, and notes with verified proofs. None of this proves the Collatz conjecture.

## Contents

| Path | What it is |
|---|---|
| `christoffel-neighbourhood/` | Working notes (`.tex` / `.pdf`) showing that no word one move from a Christoffel word satisfies the Collatz cycle divisibility $(2^A-3^r)\mid B$, for every $(r,A)$, plus extensions. The Lean proofs are in `christoffel-neighbourhood/lean/`. |
| `papers-lean/` | Formalizations of results from the literature (Terras, Böhm–Sontacchi, Crandall, Eliahou, Steiner, Simons, Simons–de Weger, Hercher, Halbeisen–Hungerbühler, an irrationality measure for $\log_2 3$, verified ranges). There is one folder per source; see `papers-lean/README.md`. |
| `shared-lean/` | Common definitions and lemmas: the Collatz, Terras and Syracuse maps and the equivalence of these formulations, and basic cycle facts. |

## Main results

- `NormAll.no_cycle_one_move_christoffel_all`: for all $r\ge2$ and $3^r+1<2^A$, no word one move from $\mathrm{chr}(r,A)$, other than $\mathrm{chr}(r,A)$ itself, satisfies $(2^A-3^r)\mid B(v)$.
- `NormBridge.cycle_one_move_christoffel`: hence no nontrivial positive cycle has such a valuation word.
- `NormShiftSlide.no_cycle_slide_allRA`: the same for one unit moved any distance (for $r\ge40901$, which every nontrivial cycle satisfies).

Prior work on the Christoffel case and on part of the one-move case is due to Knight, Lebel, Mghirbi and Solomon. The working notes give details.

## Building

The toolchain is Lean `v4.34.0-rc2` with Mathlib at the same tag. Each folder is a Lake library; see `lakefile.toml`.

```
lake exe cache get
lake build                # default target: ChristoffelNeighbourhood
```

A full build from scratch takes several CPU-hours, mostly for the kernel-checked verified-range certificates in `papers-lean/verified-range/`.

All theorems use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`). The only `sorry`s are deliberate:
- the Collatz conjecture itself, in `shared-lean/CollatzProof/Statement.lean`, which is open. The Terras and Syracuse forms are stated as corollaries of it.
- the target statements in `NormGoal.lean` and `NormGoalAll.lean`. These are proved exactly in `NormMain.lean` and `NormAll.lean`.
