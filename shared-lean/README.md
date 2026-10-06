# shared-lean

Common infrastructure used by `papers-lean/*` and `christoffel-neighbourhood/lean`:
- `CollatzProof/`: the problem statement (the maps `C` and `T`), parity lemmas, the equivalence of the `C` and `T` formulations, and the Syracuse map `S` with its equivalence (`Syracuse`);
- `CollatzSearch/`: cycle basics, the Terras affine identity, the odd-step cocycle, product and remainder bounds, cycle minimum and maximum facts, gas-station rotation, milestone statements, and the swap/slide S-unit lemmas (SwapCore, SwapExclusion).

This is one Lake library, `SharedLean`; see `../lakefile.toml`.
