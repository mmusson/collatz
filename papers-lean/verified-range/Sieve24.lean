/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import Sieve24Part0
import Sieve24Part1
import Sieve24Part2
import Sieve24Part3
import Sieve24Part4
import Sieve24Part5
import Sieve24Part6
import Sieve24Part7

/-!
# Verified descent below `2^24`

In this file we assemble the eight certificate files `Sieve24Part0`, …, `Sieve24Part7` into
`DescRange 2 (2^24)`. The certificates are 288 `decide +kernel` checks of the sieve `sv` of
`Sieve.lean`, with `K = 20`, `N = 16`, fuel 400, and forced-bit patterns modulo `2^14`.

## Main results

- `descRange_24`: every `m` with `2 ≤ m < 2^24` has a `T`-iterate below `m`.
- `min_orbit_ge_24`: the minimum `m > 1` of a `T`-orbit satisfies `2^24 ≤ m`.
-/

namespace Collatz
open CollatzProof

theorem sieve24_roots : RootsOK 400 16 2 20 14 0 (2^14) := by
  have h := rootsOK_append sieve24_part0 <| rootsOK_append sieve24_part1 <|
    rootsOK_append sieve24_part2 <| rootsOK_append sieve24_part3 <|
    rootsOK_append sieve24_part4 <| rootsOK_append sieve24_part5 <|
    rootsOK_append sieve24_part6 sieve24_part7
  simpa using h

/-- **Verified range.** Every `m` with `2 ≤ m < 2^24` descends below itself under `T`. -/
theorem descRange_24 : DescRange 2 (2^24) := by
  have := descRange_of_roots sieve24_roots
  simpa using this

/-- The minimum `m > 1` of a `T`-orbit satisfies `2^24 ≤ m`. -/
theorem min_orbit_ge_24 {m : ℕ} (hm : 1 < m) (hmin : ∀ j, m ≤ T^[j] m) : 2^24 ≤ m :=
  min_orbit_ge_of_descRange descRange_24 hm hmin

end Collatz
