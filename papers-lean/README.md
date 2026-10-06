# papers-lean

Lean 4 + Mathlib formalizations of results from the Collatz-cycle literature. They are dependencies of `../christoffel-neighbourhood/lean`. Each folder is a separate Lake library (see `../lakefile.toml`) holding its `.lean` files directly; module names are the file names, e.g. `import Crandall`.

| Folder | Source | Modules |
|---|---|---|
| `terras-1976` | Terras, *Acta Arith.* 30 (1976): stopping time, backward congruence | StoppingTime, BackCong |
| `bohm-sontacchi-1978` | Böhm–Sontacchi (1978): the cycle equation for parity words | CycleWord, WordAlgebra |
| `crandall-1978` | Crandall, *Math. Comp.* 32 (1978): odd-step lower bounds, strengthened via the Eliahou method | OddStepBound, Crandall |
| `eliahou-1993` | Eliahou, *Discrete Math.* 118 (1993): Farey decomposition of cycle parameters, certified gap lemmas for $2^A-3^r$ | Farey, FareyStretch, FareyDecomp, Farey24, Farey25, FareyBridge, FareyBig*, … |
| `steiner-1977` | Steiner (1977/78): no nontrivial 1-circuits (finite range) | OneCircuit |
| `simons-2005` | Simons, *Math. Comp.* 74 (2005): 2-circuits (finite range) | TwoCircuit |
| `simons-de-weger-2005` | Simons–de Weger, *Acta Arith.* 117 (2005): the $m$-cycle method and run bounds | Runs, RunsCert, RunsRotate, RunsBridge, RunGrowth, MRuns, RunsWindow, RunsLog, RunsTail, CRuns, FiniteRuns, FewRunsUncond |
| `hercher-2023` | Hercher, *J. Integer Seq.* 26 (2023): merge lemma | Merge |
| `halbeisen-hungerbuhler-1997` | Halbeisen–Hungerbühler, *Acta Arith.* 78 (1997): Christoffel bound for cycle minima | ChristoffelMin |
| `irrationality-measure-log2-3` | Effective irrationality measure of $\log_2 3$ via a Hata/Rhin-type Padé family, and its consequences (cycle minimum polynomial in the length) | Pade*, LcmBound, LcmCheb, SignSplit(R), TypeIITransfer, Transfer, IrrMeasure, CycleLenPoly, CycleLenPoly59 |
| `laurent-mignotte-nesterenko-1995` | Conditional interfaces to Laurent–Mignotte–Nesterenko-type linear-form bounds | LMN, LinForm, SchemeBridge |
| `verified-range` | Kernel-checked verification that every $n<2^{20}\cdot280$ descends (residue-tree sieve), plus the published bounds of Dunn 1973 and Coxeter 1971 | Descent, Sieve, VerifiedRange, PublishedBounds, Sieve24/25/29 (+ certificate parts) |

Some files are formalizations of classical results; others are partial or conditional versions. Each file's header comment states its status.

**Build time.** The `Sieve29Part*` certificate files are checked with `decide +kernel`. They take several CPU-hours in total.
