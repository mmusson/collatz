/-
Copyright (c) 2026 Mike Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mike Musson
-/
import CollatzProof.Equivalence

/-!
# The Syracuse formulation

The Syracuse map acts on odd numbers and removes *all* factors of two after each
`3n + 1` step:
`S n = (3n + 1) / 2^{v₂(3n + 1)}`.
It is the map whose orbits are the odd members of a Collatz orbit.

This file defines `S` and proves that, from an odd starting point, the Syracuse
orbit reaches `1` exactly when the accelerated orbit does, and hence exactly when
the classical one does. As in `Equivalence`, this is bookkeeping, not progress:
the Syracuse conjecture is a corollary of `collatz_conjecture`, and the two are
equivalent.

## Main definitions

* `CollatzProof.oddPart` — `n / 2^{v₂(n)}` for `n > 0` (and `0 ↦ 0`), computed by
  repeated halving with fuel `n`, so that it reduces in the kernel.
* `CollatzProof.S` — the Syracuse map `n ↦ oddPart (3n + 1)`. It is meant for odd
  `n`; on even inputs it is defined but has no dynamical meaning.

## Main results

* `iterate_T_eq_oddPart` — the `T`-orbit of `x > 0` reaches `oddPart x` by halving
  steps through even, positive values.
* `exists_iterate_T_eq_S` — for odd `n`, one `S`-step is a positive number of
  `T`-steps, and the skipped values are even and positive (so never `1`).
* `reaches_one_iff_syracuse` — for odd `n`, `T` reaches `1` iff `S` does. Proved.
* `collatz_iff_syracuse` — the quantified form, against `C`. Proved.
* `syracuse_conjecture` — corollary of the (still open) `collatz_conjecture`.
-/

namespace CollatzProof

/-- Repeated halving with explicit fuel: strip factors of two from `x` while
`x` is even and positive, at most `k` times. -/
def oddPartAux : ℕ → ℕ → ℕ
  | 0, x => x
  | k + 1, x => if x % 2 = 0 ∧ 0 < x then oddPartAux k (x / 2) else x

/-- The odd part of `x`: `x / 2^{v₂(x)}` for `x > 0`, and `0` for `x = 0`. Fuel `x`
suffices, since each halving at least halves a positive number. -/
def oddPart (x : ℕ) : ℕ := oddPartAux x x

/-- **The Syracuse map** `n ↦ (3n + 1) / 2^{v₂(3n + 1)}`, intended for odd `n`. -/
def S (n : ℕ) : ℕ := oddPart (3 * n + 1)

section Sanity

/-- `27 ↦ 41`: `3·27 + 1 = 82 = 2·41`. -/
example : S 27 = 41 := by decide

/-- `5 ↦ 1`: `16 = 2^4`, so the whole power of two is stripped in one step. -/
example : S 5 = 1 := by decide

/-- `1` is a fixed point of `S`: `3·1 + 1 = 4 = 2^2`. The trivial cycle has length
one here, against two for `T` and three for `C`. -/
example : S 1 = 1 := by decide

end Sanity

/-- Halving with enough fuel follows the `T`-orbit. If `0 < x ≤ k`, then the
`T`-orbit of `x` reaches `oddPartAux k x` after some `j` steps, every value before
that is even and positive, and the result is odd. -/
theorem iterate_T_eq_oddPartAux :
    ∀ k x, 0 < x → x ≤ k →
      oddPartAux k x % 2 = 1 ∧
      ∃ j, T^[j] x = oddPartAux k x ∧ ∀ i < j, T^[i] x % 2 = 0 ∧ 0 < T^[i] x := by
  intro k
  induction k with
  | zero => intro x hx hk; omega
  | succ k ih =>
    intro x hx hk
    by_cases he : x % 2 = 0
    · -- `x` is even and positive: one halving step, then recurse on `x / 2`.
      have hx2 : 0 < x / 2 := by omega
      have hk2 : x / 2 ≤ k := by omega
      obtain ⟨hodd, j, hj, hint⟩ := ih (x / 2) hx2 hk2
      have hstep : oddPartAux (k + 1) x = oddPartAux k (x / 2) := by
        simp [oddPartAux, he, hx]
      refine ⟨hstep ▸ hodd, j + 1, ?_, ?_⟩
      · rw [Function.iterate_succ_apply, T_of_even he, hstep]; exact hj
      · intro i hi
        rcases i with _ | i
        · exact ⟨he, hx⟩
        · rw [Function.iterate_succ_apply, T_of_even he]
          exact hint i (by omega)
    · -- `x` is odd: nothing to strip.
      have hstep : oddPartAux (k + 1) x = x := by simp [oddPartAux, he]
      refine ⟨by rw [hstep]; omega, 0, by rw [hstep]; rfl, fun i hi => by omega⟩

/-- The `T`-orbit of `x > 0` reaches `oddPart x`, which is odd, by halving steps
through even, positive values. -/
theorem iterate_T_eq_oddPart {x : ℕ} (hx : 0 < x) :
    oddPart x % 2 = 1 ∧
      ∃ j, T^[j] x = oddPart x ∧ ∀ i < j, T^[i] x % 2 = 0 ∧ 0 < T^[i] x :=
  iterate_T_eq_oddPartAux x x hx le_rfl

/-- `S n` is odd (for every `n`, since `3n + 1 > 0`). -/
theorem S_odd (n : ℕ) : S n % 2 = 1 := (iterate_T_eq_oddPart (by omega)).1

/-- For odd `n`, `T n = T (3n + 1)`: both equal `(3n + 1) / 2`. -/
theorem T_eq_T_three_mul_add_one {n : ℕ} (h : n % 2 = 1) : T n = T (3 * n + 1) := by
  rw [T_of_odd h, T_of_even (even_three_mul_add_one h)]

/-- **One `S`-step is a positive number of `T`-steps.** For odd `n` there is
`e ≥ 1` with `T^[e] n = S n`, and every value strictly between (`0 < i < e`) is even
and positive, hence never `1`. -/
theorem exists_iterate_T_eq_S {n : ℕ} (h : n % 2 = 1) :
    ∃ e, 0 < e ∧ T^[e] n = S n ∧ ∀ i, 0 < i → i < e → T^[i] n % 2 = 0 ∧ 0 < T^[i] n := by
  obtain ⟨hodd, j, hj, hint⟩ := iterate_T_eq_oddPart (x := 3 * n + 1) (by omega)
  -- The orbits of `n` and `3n + 1` agree from step one on.
  have hagree : ∀ i, 0 < i → T^[i] n = T^[i] (3 * n + 1) := by
    intro i hi
    obtain ⟨i, rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, T_eq_T_three_mul_add_one h]
  -- `j > 0`, because `3n + 1` is even while its odd part is odd.
  have hj0 : 0 < j := by
    rcases Nat.eq_zero_or_pos j with rfl | hpos
    · have h3 := even_three_mul_add_one h
      simp only [Function.iterate_zero, id] at hj
      rw [← hj] at hodd; omega
    · exact hpos
  refine ⟨j, hj0, by rw [hagree j hj0]; exact hj, fun i hi hij => ?_⟩
  rw [hagree i hi]; exact hint i hij

/-- If the Syracuse orbit of an odd `n` reaches `1`, so does the accelerated orbit:
expand each `S`-step into its `T`-steps. -/
theorem reaches_T_of_reaches_S : ∀ k n : ℕ, n % 2 = 1 → S^[k] n = 1 → ∃ m, T^[m] n = 1 := by
  intro k
  induction k with
  | zero => intro n _ hk; exact ⟨0, hk⟩
  | succ k ih =>
    intro n hn hk
    rw [Function.iterate_succ_apply] at hk
    obtain ⟨m, hm⟩ := ih (S n) (S_odd n) hk
    obtain ⟨e, -, he, -⟩ := exists_iterate_T_eq_S hn
    exact ⟨m + e, by rw [Function.iterate_add_apply, he]; exact hm⟩

/-- If the accelerated orbit of an odd `n` reaches `1`, so does the Syracuse orbit.

As in `reaches_T_of_reaches_C`, the point is that the `T`-steps skipped by one
`S`-step land on even positive numbers, never on `1`. So the `T`-orbit cannot
terminate inside a step that the Syracuse orbit jumps over. -/
theorem reaches_S_of_reaches_T : ∀ m n : ℕ, n % 2 = 1 → T^[m] n = 1 → ∃ k, S^[k] n = 1 := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro n hn hm
    by_cases h1 : n = 1
    · exact ⟨0, by simp [h1]⟩
    obtain ⟨e, he0, he, hint⟩ := exists_iterate_T_eq_S hn
    -- The `T`-orbit cannot hit `1` before step `e`.
    have hme : e ≤ m := by
      by_contra hle
      have hlt : m < e := Nat.lt_of_not_le hle
      rcases Nat.eq_zero_or_pos m with rfl | hmpos
      · exact h1 hm
      · have := (hint m hmpos hlt).1; omega
    obtain ⟨m', rfl⟩ : ∃ m', m = m' + e := ⟨m - e, by omega⟩
    rw [Function.iterate_add_apply, he] at hm
    obtain ⟨k, hk⟩ := ih m' (by omega) (S n) (S_odd n) hm
    exact ⟨k + 1, by rw [Function.iterate_succ_apply]; exact hk⟩

/-- **From an odd start, the accelerated and Syracuse orbits reach `1` together.** -/
theorem reaches_one_iff_syracuse {n : ℕ} (hn : n % 2 = 1) :
    (∃ m, T^[m] n = 1) ↔ (∃ k, S^[k] n = 1) :=
  ⟨fun ⟨m, hm⟩ => reaches_S_of_reaches_T m n hn hm,
   fun ⟨k, hk⟩ => reaches_T_of_reaches_S k n hn hk⟩

/-- **The classical conjecture is equivalent to the Syracuse conjecture.** The
Syracuse side quantifies only over odd numbers; an even start first halves down to
its odd part. -/
theorem collatz_iff_syracuse :
    (∀ n, 0 < n → ∃ k, C^[k] n = 1) ↔ (∀ n, n % 2 = 1 → ∃ k, S^[k] n = 1) := by
  constructor
  · intro h n hn
    exact (reaches_one_iff_syracuse hn).mp ((reaches_one_iff n).mp (h n (by omega)))
  · intro h n hn
    rw [reaches_one_iff]
    obtain ⟨hodd, j, hj, -⟩ := iterate_T_eq_oddPart hn
    obtain ⟨m, hm⟩ := (reaches_one_iff_syracuse hodd).mpr (h _ hodd)
    exact ⟨m + j, by rw [Function.iterate_add_apply, hj]; exact hm⟩

/-- **The Collatz conjecture, Syracuse form.** Every odd positive integer reaches
`1` under the Syracuse map.

A corollary of `collatz_conjecture`, so its `#print axioms` report inherits
`sorryAx` from that one hole and from nowhere else. -/
theorem syracuse_conjecture (n : ℕ) (hn : n % 2 = 1) : ∃ k, S^[k] n = 1 :=
  collatz_iff_syracuse.mp collatz_conjecture n hn

section Transport

set_option maxRecDepth 100000 in
/-- The Syracuse orbit of `27` reaches `1` after `41` steps, one per odd member of
the classical orbit other than the final `1`. Push it to the accelerated side. -/
example : ∃ m, T^[m] 27 = 1 := (reaches_one_iff_syracuse (by decide)).mpr ⟨41, by decide⟩

end Transport

end CollatzProof

-- The equivalences are genuinely proved: no `sorryAx`.
#print axioms CollatzProof.reaches_one_iff_syracuse
#print axioms CollatzProof.collatz_iff_syracuse

-- The Syracuse form inherits exactly one hole, from the classical conjecture.
#print axioms CollatzProof.syracuse_conjecture
