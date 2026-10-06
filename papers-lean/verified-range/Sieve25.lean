import Sieve24
import Sieve25Part0
import Sieve25Part1
import Sieve25Part2
import Sieve25Part3
import Sieve25Part4
import Sieve25Part5
import Sieve25Part6
import Sieve25Part7

/-!
# Verified descent below `2^25`

Assembles the eight kernel-certificate files `Sieve25Part0..7` (299 `decide +kernel` blocks of
the unchanged residue-tree sieve `sv` of `Sieve.lean`, with `lo = 2^24`, `K = 20`, `N = 32`,
fuel 400, forced-bit patterns mod `2^14`; about 14 min kernel CPU in total) into
`DescRange (2^24) (2^25)`, and combines it with `FareyDecomp`/`Sieve` `descRange_24` to get `DescRange 2 (2^25)`:
every `m ∈ [2, 2^25)` has a `T`-iterate below `m`. Kernel reduction only (`decide +kernel`).

Classical and mathematically routine (the literature has verified far beyond `2^68`); used for the
published-bound formalizations in `PublishedBounds.lean`.
-/

namespace Collatz
open CollatzProof

theorem sieve25_roots : RootsOK 400 32 16777216 20 14 0 (2^14) := by
  have h := rootsOK_append sieve25_part0 <| rootsOK_append sieve25_part1 <|
    rootsOK_append sieve25_part2 <| rootsOK_append sieve25_part3 <|
    rootsOK_append sieve25_part4 <| rootsOK_append sieve25_part5 <|
    rootsOK_append sieve25_part6 sieve25_part7
  simpa using h

/-- Every `m` with `2^24 ≤ m < 2^25` descends below itself under `T` (kernel sieve). -/
theorem descRange_24_25 : DescRange (2^24) (2^25) := by
  have := descRange_of_roots sieve25_roots
  intro m h1 h2
  exact this m (by norm_num at h1 ⊢; omega) (by norm_num at h2 ⊢; omega)

/-- **Verified range.** Every `m` with `2 ≤ m < 2^25` descends below itself under `T`. -/
theorem descRange_25 : DescRange 2 (2^25) := by
  intro m h1 h2
  by_cases h : m < 2^24
  · exact descRange_24 m h1 h
  · exact descRange_24_25 m (by omega) h2

/-- The minimum `m > 1` of a `T`-orbit satisfies `2^25 ≤ m`. -/
theorem min_orbit_ge_25 {m : ℕ} (hm : 1 < m) (hmin : ∀ j, m ≤ T^[j] m) : 2^25 ≤ m :=
  min_orbit_ge_of_descRange descRange_25 hm hmin

end Collatz

#print axioms Collatz.sieve25_roots
#print axioms Collatz.descRange_24_25
#print axioms Collatz.descRange_25
#print axioms Collatz.min_orbit_ge_25
