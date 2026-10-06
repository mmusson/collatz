import CollatzSearch.Sieve25
import CollatzSearch.Sieve29Part0
import CollatzSearch.Sieve29Part1
import CollatzSearch.Sieve29Part2
import CollatzSearch.Sieve29Part3
import CollatzSearch.Sieve29Part4
import CollatzSearch.Sieve29Part5
import CollatzSearch.Sieve29Part6
import CollatzSearch.Sieve29Part7
import CollatzSearch.Sieve29Part8
import CollatzSearch.Sieve29Part9
import CollatzSearch.Sieve29Part10
import CollatzSearch.Sieve29Part11
import CollatzSearch.Sieve29Part12
import CollatzSearch.Sieve29Part13
import CollatzSearch.Sieve29Part14
import CollatzSearch.Sieve29Part15
import CollatzSearch.Sieve29Part16
import CollatzSearch.Sieve29Part17
import CollatzSearch.Sieve29Part18
import CollatzSearch.Sieve29Part19
import CollatzSearch.Sieve29Part20
import CollatzSearch.Sieve29Part21
import CollatzSearch.Sieve29Part22
import CollatzSearch.Sieve29Part23
import CollatzSearch.Sieve29Part24
import CollatzSearch.Sieve29Part25
import CollatzSearch.Sieve29Part26
import CollatzSearch.Sieve29Part27
import CollatzSearch.Sieve29Part28
import CollatzSearch.Sieve29Part29
import CollatzSearch.Sieve29Part30
import CollatzSearch.Sieve29Part31
import CollatzSearch.Sieve29Part32
import CollatzSearch.Sieve29Part33
import CollatzSearch.Sieve29Part34
import CollatzSearch.Sieve29Part35
import CollatzSearch.Sieve29Part36
import CollatzSearch.Sieve29Part37
import CollatzSearch.Sieve29Part38
import CollatzSearch.Sieve29Part39
import CollatzSearch.Sieve29Part40
import CollatzSearch.Sieve29Part41
import CollatzSearch.Sieve29Part42
import CollatzSearch.Sieve29Part43
import CollatzSearch.Sieve29Part44
import CollatzSearch.Sieve29Part45
import CollatzSearch.Sieve29Part46
import CollatzSearch.Sieve29Part47
import CollatzSearch.Sieve29Part48
import CollatzSearch.Sieve29Part49
import CollatzSearch.Sieve29Part50
import CollatzSearch.Sieve29Part51
import CollatzSearch.Sieve29Part52
import CollatzSearch.Sieve29Part53
import CollatzSearch.Sieve29Part54
import CollatzSearch.Sieve29Part55
import CollatzSearch.Sieve29Part56
import CollatzSearch.Sieve29Part57
import CollatzSearch.Sieve29Part58
import CollatzSearch.Sieve29Part59
import CollatzSearch.Sieve29Part60
import CollatzSearch.Sieve29Part61
import CollatzSearch.Sieve29Part62
import CollatzSearch.Sieve29Part63

/-!
# Verified descent below `2^20 · 280 = 35 · 2^23 = 293601280`

Assembles the 64 kernel-certificate files `Sieve29Part0..63` (919 `decide +kernel` blocks of the
unchanged residue-tree sieve `sv` of `Sieve.lean`, with `lo = 2^25`, `K = 20`, `N = 280`,
fuel 400, forced-bit patterns mod `2^14`; generator `Scratch/sieve_gen/gen29.py`, all `2^14`
patterns pre-simulated in Python with fuel 400) into `DescRange (2^25) (2^20 * 280)`, and
combines it with `Sieve25`/`PublishedBounds` `descRange_25` to get `DescRange 2 (2^20 * 280)`: every `m` with
`2 ≤ m < 293601280` has a `T`-iterate below `m`.  Kernel reduction only (`decide +kernel`).

Classical and mathematically routine (the literature has verified far beyond `2^68`).  The
threshold `293601280 ≈ 17.5 · 2^24` is chosen because it is just above the `≈ 17.04 · 2^24`
needed to pass the Farey pair `24727/15601` (Crandall 1978's bound, `Crandall.lean`).
Not Goal progress.
-/

namespace CollatzSearch
open CollatzProof

theorem sieve29_roots : RootsOK 400 280 33554432 20 14 0 (2^14) := by
  have h :=
    rootsOK_append sieve29_part0 <|
    rootsOK_append sieve29_part1 <|
    rootsOK_append sieve29_part2 <|
    rootsOK_append sieve29_part3 <|
    rootsOK_append sieve29_part4 <|
    rootsOK_append sieve29_part5 <|
    rootsOK_append sieve29_part6 <|
    rootsOK_append sieve29_part7 <|
    rootsOK_append sieve29_part8 <|
    rootsOK_append sieve29_part9 <|
    rootsOK_append sieve29_part10 <|
    rootsOK_append sieve29_part11 <|
    rootsOK_append sieve29_part12 <|
    rootsOK_append sieve29_part13 <|
    rootsOK_append sieve29_part14 <|
    rootsOK_append sieve29_part15 <|
    rootsOK_append sieve29_part16 <|
    rootsOK_append sieve29_part17 <|
    rootsOK_append sieve29_part18 <|
    rootsOK_append sieve29_part19 <|
    rootsOK_append sieve29_part20 <|
    rootsOK_append sieve29_part21 <|
    rootsOK_append sieve29_part22 <|
    rootsOK_append sieve29_part23 <|
    rootsOK_append sieve29_part24 <|
    rootsOK_append sieve29_part25 <|
    rootsOK_append sieve29_part26 <|
    rootsOK_append sieve29_part27 <|
    rootsOK_append sieve29_part28 <|
    rootsOK_append sieve29_part29 <|
    rootsOK_append sieve29_part30 <|
    rootsOK_append sieve29_part31 <|
    rootsOK_append sieve29_part32 <|
    rootsOK_append sieve29_part33 <|
    rootsOK_append sieve29_part34 <|
    rootsOK_append sieve29_part35 <|
    rootsOK_append sieve29_part36 <|
    rootsOK_append sieve29_part37 <|
    rootsOK_append sieve29_part38 <|
    rootsOK_append sieve29_part39 <|
    rootsOK_append sieve29_part40 <|
    rootsOK_append sieve29_part41 <|
    rootsOK_append sieve29_part42 <|
    rootsOK_append sieve29_part43 <|
    rootsOK_append sieve29_part44 <|
    rootsOK_append sieve29_part45 <|
    rootsOK_append sieve29_part46 <|
    rootsOK_append sieve29_part47 <|
    rootsOK_append sieve29_part48 <|
    rootsOK_append sieve29_part49 <|
    rootsOK_append sieve29_part50 <|
    rootsOK_append sieve29_part51 <|
    rootsOK_append sieve29_part52 <|
    rootsOK_append sieve29_part53 <|
    rootsOK_append sieve29_part54 <|
    rootsOK_append sieve29_part55 <|
    rootsOK_append sieve29_part56 <|
    rootsOK_append sieve29_part57 <|
    rootsOK_append sieve29_part58 <|
    rootsOK_append sieve29_part59 <|
    rootsOK_append sieve29_part60 <|
    rootsOK_append sieve29_part61 <|
    rootsOK_append sieve29_part62 sieve29_part63
  simpa using h

/-- Every `m` with `2^25 ≤ m < 2^20 · 280` descends below itself under `T` (kernel sieve). -/
theorem descRange_25_29 : DescRange (2^25) (2^20 * 280) := by
  have := descRange_of_roots sieve29_roots
  intro m h1 h2
  exact this m (by norm_num at h1 ⊢; omega) (by norm_num at h2 ⊢; omega)

/-- **Verified range.** Every `m` with `2 ≤ m < 2^20 · 280 = 293601280` descends below itself
under `T`. -/
theorem descRange_29 : DescRange 2 (2^20 * 280) := by
  intro m h1 h2
  by_cases h : m < 2^25
  · exact descRange_25 m h1 h
  · exact descRange_25_29 m (by omega) h2

/-- The minimum `m > 1` of a `T`-orbit satisfies `2^20 · 280 ≤ m`. -/
theorem min_orbit_ge_29 {m : ℕ} (hm : 1 < m) (hmin : ∀ j, m ≤ T^[j] m) : 2^20 * 280 ≤ m :=
  min_orbit_ge_of_descRange descRange_29 hm hmin

end CollatzSearch

#print axioms CollatzSearch.sieve29_roots
#print axioms CollatzSearch.descRange_25_29
#print axioms CollatzSearch.descRange_29
#print axioms CollatzSearch.min_orbit_ge_29
