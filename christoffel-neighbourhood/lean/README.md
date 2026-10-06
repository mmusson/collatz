# Christoffel neighbourhood: Lean files

Lean 4 proofs for `../christoffel-neighbourhood-working-notes.tex`. This is the Lake library `ChristoffelNeighbourhood`, defined in `../../lakefile.toml`. It depends on `../../shared-lean` and `../../papers-lean`.

Main entry points:
- `NormAll.no_cycle_one_move_christoffel_all`: radius-1 exclusion for all $(r,A)$;
- `NormBridge.cycle_one_move_christoffel`: the cycle form;
- `NormShiftSlide.no_cycle_slide_allRA`: a unit slid any distance.

`NormGoal.lean` and `NormGoalAll.lean` hold the fixed target statements, proved by `sorry`. `NormMain.lean` and `NormAll.lean` prove exactly these statements.

**Build:** from the repository root, run `lake exe cache get`, then `lake build ChristoffelNeighbourhood`.
