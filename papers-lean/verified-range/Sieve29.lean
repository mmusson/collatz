/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import Sieve25
import Sieve29Part0
import Sieve29Part1
import Sieve29Part2
import Sieve29Part3
import Sieve29Part4
import Sieve29Part5
import Sieve29Part6
import Sieve29Part7
import Sieve29Part8
import Sieve29Part9
import Sieve29Part10
import Sieve29Part11
import Sieve29Part12
import Sieve29Part13
import Sieve29Part14
import Sieve29Part15
import Sieve29Part16
import Sieve29Part17
import Sieve29Part18
import Sieve29Part19
import Sieve29Part20
import Sieve29Part21
import Sieve29Part22
import Sieve29Part23
import Sieve29Part24
import Sieve29Part25
import Sieve29Part26
import Sieve29Part27
import Sieve29Part28
import Sieve29Part29
import Sieve29Part30
import Sieve29Part31
import Sieve29Part32
import Sieve29Part33
import Sieve29Part34
import Sieve29Part35
import Sieve29Part36
import Sieve29Part37
import Sieve29Part38
import Sieve29Part39
import Sieve29Part40
import Sieve29Part41
import Sieve29Part42
import Sieve29Part43
import Sieve29Part44
import Sieve29Part45
import Sieve29Part46
import Sieve29Part47
import Sieve29Part48
import Sieve29Part49
import Sieve29Part50
import Sieve29Part51
import Sieve29Part52
import Sieve29Part53
import Sieve29Part54
import Sieve29Part55
import Sieve29Part56
import Sieve29Part57
import Sieve29Part58
import Sieve29Part59
import Sieve29Part60
import Sieve29Part61
import Sieve29Part62
import Sieve29Part63

/-!
# Verified descent below `2^20 · 280 = 293601280`

In this file we assemble the 64 certificate files `Sieve29Part0`, …, `Sieve29Part63` into
`DescRange (2^25) (2^20 · 280)`, and combine it with `descRange_25`. The certificates are 919
`decide +kernel` checks of the sieve `sv` of `Sieve.lean`, with `lo = 2^25`, `K = 20`, `N = 280`,
fuel 400, and forced-bit patterns modulo `2^14`.

The bound `293601280 ≈ 17.5 · 2^24` is just above the `≈ 17.04 · 2^24` needed for the Farey pair
`24727/15601`, which gives Crandall's bound in `Crandall.lean`.

## Main results

- `descRange_25_29`: every `m` with `2^25 ≤ m < 2^20 · 280` has a `T`-iterate below `m`.
- `descRange_29`: every `m` with `2 ≤ m < 2^20 · 280` has a `T`-iterate below `m`.
- `min_orbit_ge_29`: the minimum `m > 1` of a `T`-orbit satisfies `2^20 · 280 ≤ m`.
-/

namespace Collatz
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

end Collatz
