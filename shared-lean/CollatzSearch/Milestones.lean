import CollatzProof.Basic
import Mathlib.Data.Set.Card

/-!
# Milestones — intermediate targets, weaker than `Goal.lean` — DO NOT EDIT THE STATEMENTS

Fixed statements of results that are far weaker than `no_nontrivial_cycles` but still
significant.  A milestone is reached only when a theorem proving one of these `Prop`s
(for the stated parameter) compiles in another file with axioms among
`propext`, `Classical.choice`, `Quot.sound`.

* `FinitelyManyCycles` — **open in the literature**; a proof is a major result.
* `AtMostCycles N` — **open for every `N`**; `AtMostCycles 1` is equivalent to the Goal.
* `CycleLengthAtLeast L` — known in the literature for large `L` (Eliahou 1993, Hercher 2023);
  a milestone only for `L` beyond the published bounds, or as the first formal proof of a
  published bound.
* `CycleMinAbove B` — known computationally for `B = 2^68` or more; same caveat.

`CycleMinima` has one element per cycle (its minimum), so it counts the cycles.
-/

namespace CollatzSearch
open CollatzProof

/-- Positive periodic points of the classical map `C`. -/
def CyclePoints : Set ℕ := {n | 0 < n ∧ ∃ ℓ, 0 < ℓ ∧ C^[ℓ] n = n}

/-- Cycle minima: one representative per cycle. -/
def CycleMinima : Set ℕ := {n | n ∈ CyclePoints ∧ ∀ k, n ≤ C^[k] n}

/-- **M1.** There are finitely many Collatz cycles.  Open. -/
def FinitelyManyCycles : Prop := CycleMinima.Finite

/-- **M2.** There are at most `N` Collatz cycles, counting the trivial one.  Open. -/
def AtMostCycles (N : ℕ) : Prop := CycleMinima.Finite ∧ CycleMinima.ncard ≤ N

/-- **M3.** Every nontrivial cycle has (classical) period at least `L`. -/
def CycleLengthAtLeast (L : ℕ) : Prop :=
  ∀ n ℓ : ℕ, 0 < n → 0 < ℓ → C^[ℓ] n = n → n ≠ 1 → n ≠ 2 → n ≠ 4 → L ≤ ℓ

/-- **M4.** Every element of a nontrivial cycle exceeds `B`. -/
def CycleMinAbove (B : ℕ) : Prop :=
  ∀ n ∈ CyclePoints, n ≠ 1 → n ≠ 2 → n ≠ 4 → B < n

/-- Sanity: the trivial cycle is present, so `AtMostCycles 0` is false. -/
theorem one_mem_cycleMinima : 1 ∈ CycleMinima := by
  refine ⟨⟨Nat.one_pos, 3, by decide, by decide⟩, fun k => ?_⟩
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply']
    set m := C^[k] 1
    unfold C; split_ifs <;> omega

theorem not_atMostCycles_zero : ¬ AtMostCycles 0 := by
  rintro ⟨hf, h0⟩
  have := (Set.ncard_pos hf).2 ⟨1, one_mem_cycleMinima⟩
  omega

end CollatzSearch

#print axioms CollatzSearch.not_atMostCycles_zero
