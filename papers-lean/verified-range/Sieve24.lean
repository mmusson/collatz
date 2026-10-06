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

Assembles the eight kernel-certificate files `Sieve24Part0..7` (288 `decide +kernel` blocks of
the residue-tree sieve `sv` with `K = 20`, `N = 16`, fuel 400, forced-bit patterns mod `2^14`)
into `DescRange 2 (2^24)`: every `m ∈ [2, 2^24)` has a `T`-iterate below `m`.  Consequence
`min_orbit_ge_24`: the minimum `m > 1` of a `T`-orbit is `≥ 2^24`.

Classical (Oliveira e Silva-style sieve: Terras classes mod `2^K` that descend at the class level
are discharged at once; the survivors are checked individually from `T^K n = a y + c`).  It only
gains a constant factor over direct enumeration; the literature has verified far beyond `2^68`.
-/

namespace Collatz
open CollatzProof

theorem sieve24_roots : RootsOK 400 16 2 20 14 0 (2^14) := by
  have h := rootsOK_append sieve24_part0 <| rootsOK_append sieve24_part1 <|
    rootsOK_append sieve24_part2 <| rootsOK_append sieve24_part3 <|
    rootsOK_append sieve24_part4 <| rootsOK_append sieve24_part5 <|
    rootsOK_append sieve24_part6 sieve24_part7
  simpa using h

/-- **Verified range (T2).** Every `m` with `2 ≤ m < 2^24` descends below itself under `T`. -/
theorem descRange_24 : DescRange 2 (2^24) := by
  have := descRange_of_roots sieve24_roots
  simpa using this

/-- The minimum `m > 1` of a `T`-orbit satisfies `2^24 ≤ m`. -/
theorem min_orbit_ge_24 {m : ℕ} (hm : 1 < m) (hmin : ∀ j, m ≤ T^[j] m) : 2^24 ≤ m :=
  min_orbit_ge_of_descRange descRange_24 hm hmin

end Collatz

#print axioms Collatz.sieve24_0_0
#print axioms Collatz.sieve24_roots
#print axioms Collatz.descRange_24
#print axioms Collatz.min_orbit_ge_24
