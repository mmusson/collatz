/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import FareyStretch
import Mathlib.Tactic

/-!
# Certified interval arithmetic for `3^q / 2^p`

Let `R q p = 3^q / 2^p ∈ ℚ`. A bracket `Br P A B q p` says `A/2^P ≤ R q p ≤ B/2^P`. Brackets
propagate along `(q, p) ↦ a(q₁, p₁) + (q₀, p₀)` via `R_new = R₁^a · R₀` (`br_step`), with purely
integer side conditions of about `P · a` bits. Readout lemmas turn a bracket into `3^q < 2^p`,
`2^p < 3^q`, or a relative gap `2^p ≤ 2^s (2^p − 3^q)`. No large power is ever evaluated: `3^q`
only appears symbolically.

These lemmas are used by the brackets of `FareyBigChain` and by `FareyBig`.

## Main definitions

- `R q p`: the rational number `3^q / 2^p`.
- `Br P A B q p`: the bracket `A/2^P ≤ R q p ≤ B/2^P`.

## Main results

- `br_step`: one step of the certified recurrence.
- `three_pow_lt_of_br`, `two_pow_lt_of_br`, `gap_of_br`: readouts of a bracket.

## References

- S. Eliahou, *The 3x+1 problem: new lower bounds on nontrivial cycle lengths*, Discrete Math.
  118 (1993), 45–56.
-/

namespace Collatz

/-! ### Brackets for `3^q / 2^p` -/

/-- The rational number `R q p = 3^q / 2^p`, sealed with `irreducible_def`; it is used only
through the lemmas below. -/
irreducible_def R (q p : ℕ) : ℚ := (3:ℚ)^q / (2:ℚ)^p

theorem R_nonneg (q p : ℕ) : 0 ≤ R q p := by rw [R_def]; positivity

theorem R_rec (a q1 p1 q0 p0 : ℕ) : R (a*q1+q0) (a*p1+p0) = R q1 p1 ^ a * R q0 p0 := by
  simp only [R_def]
  rw [pow_add, pow_add, mul_comm a q1, mul_comm a p1, pow_mul, pow_mul, div_pow,
    mul_div_mul_comm]

/-- The bracket `A/2^P ≤ R q p ≤ B/2^P`. -/
def Br (P A B q p : ℕ) : Prop := (A:ℚ)/2^P ≤ R q p ∧ R q p ≤ (B:ℚ)/2^P

/-- The exact bracket for `R 0 1 = 1/2`. -/
theorem br_base_m1 : Br 384 (2^383) (2^383) 0 1 := by
  have e : ((2^383 : ℕ) : ℚ) / 2^384 = (3:ℚ)^0 / 2^1 := by
    rw [show (384:ℕ) = 383 + 1 from rfl, pow_succ]; push_cast; field_simp
  unfold Br; rw [R_def, e]; exact ⟨le_rfl, le_rfl⟩

/-- The exact bracket for `R 1 1 = 3/2`. -/
theorem br_base_0 : Br 384 (3*2^383) (3*2^383) 1 1 := by
  have e : ((3*2^383 : ℕ) : ℚ) / 2^384 = (3:ℚ)^1 / 2^1 := by
    rw [show (384:ℕ) = 383 + 1 from rfl, pow_succ]; push_cast; field_simp
  unfold Br; rw [R_def, e]; exact ⟨le_rfl, le_rfl⟩

/-! ### The recurrence -/

/-- One step of the certified recurrence: brackets for `R q₁ p₁` and `R q₀ p₀` give a bracket for
`R (a q₁ + q₀) (a p₁ + p₀)`, provided two integer inequalities hold. -/
theorem br_step {P a A0 B0 A1 B1 A2 B2 q0 p0 q1 p1 q2 p2 : ℕ}
    (h1 : Br P A1 B1 q1 p1) (h0 : Br P A0 B0 q0 p0)
    (hq : q2 = a*q1+q0) (hp : p2 = a*p1+p0)
    (hA : A2 * 2^(P*a) ≤ A1^a * A0) (hB : B1^a * B0 ≤ B2 * 2^(P*a)) :
    Br P A2 B2 q2 p2 := by
  subst hq hp
  rw [Br, R_rec]
  obtain ⟨l1, u1⟩ := h1
  obtain ⟨l0, u0⟩ := h0
  have hR1 := R_nonneg q1 p1
  have hR0 := R_nonneg q0 p0
  have hD : (0:ℚ) < 2^P := by positivity
  have hDa : (0:ℚ) < 2^(P*a) := by positivity
  have hA' : (A2:ℚ) * 2^(P*a) ≤ (A1:ℚ)^a * A0 := by exact_mod_cast hA
  have hB' : (B1:ℚ)^a * B0 ≤ (B2:ℚ) * 2^(P*a) := by exact_mod_cast hB
  have e : ((2:ℚ)^P)^a = 2^(P*a) := by rw [← pow_mul]
  have x1 : (0:ℚ) ≤ A1/2^P := by positivity
  have x0 : (0:ℚ) ≤ A0/2^P := by positivity
  constructor
  · have k1 : ((A1:ℚ)/2^P)^a * (A0/2^P) ≤ R q1 p1 ^ a * R q0 p0 :=
      mul_le_mul (pow_le_pow_left₀ x1 l1 a) l0 x0 (pow_nonneg hR1 a)
    refine le_trans ?_ k1
    rw [div_pow, e, div_mul_div_comm, div_le_div_iff₀ hD (mul_pos hDa hD)]
    nlinarith
  · have k1 : R q1 p1 ^ a * R q0 p0 ≤ ((B1:ℚ)/2^P)^a * (B0/2^P) :=
      mul_le_mul (pow_le_pow_left₀ hR1 u1 a) u0 hR0 (pow_nonneg (hR1.trans u1) a)
    refine le_trans k1 ?_
    rw [div_pow, e, div_mul_div_comm, div_le_div_iff₀ (mul_pos hDa hD) hD]
    nlinarith

/-! ### Readouts -/

/-- A bracket with upper end `< 1` gives `3^q < 2^p`. -/
theorem three_pow_lt_of_br {P A B q p : ℕ} (h : Br P A B q p) (hB : B < 2^P) : 3^q < 2^p := by
  have hB' : (B:ℚ) < 2^P := by exact_mod_cast hB
  have hD : (0:ℚ) < 2^P := by positivity
  have h1 : R q p < 1 := lt_of_le_of_lt h.2 ((div_lt_one hD).2 hB')
  rw [R_def, div_lt_one (by positivity)] at h1
  exact_mod_cast h1

/-- A bracket with lower end `> 1` gives `2^p < 3^q`. -/
theorem two_pow_lt_of_br {P A B q p : ℕ} (h : Br P A B q p) (hA : 2^P < A) : 2^p < 3^q := by
  have hA' : (2:ℚ)^P < A := by exact_mod_cast hA
  have hD : (0:ℚ) < 2^P := by positivity
  have h1 : 1 < R q p := lt_of_lt_of_le ((one_lt_div hD).2 hA') h.1
  rw [R_def, one_lt_div (by positivity)] at h1
  exact_mod_cast h1

/-- A bracket with upper end at most `1 − 2^{-s}` gives `2^p ≤ 2^s (2^p − 3^q)`. -/
theorem gap_of_br {P A B q p s : ℕ} (h : Br P A B q p) (hs : B * 2^s ≤ 2^P * (2^s - 1)) :
    2^p ≤ 2^s * (2^p - 3^q) := by
  have h1s : 1 ≤ 2^s := Nat.one_le_two_pow
  have hs' : (B:ℚ) * 2^s ≤ 2^P * (2^s - 1) := by
    have := (Nat.cast_le (α := ℚ)).2 hs
    push_cast [Nat.cast_sub h1s] at this
    exact this
  have hD : (0:ℚ) < 2^P := by positivity
  have hS : (0:ℚ) < 2^s := by positivity
  have hp : (0:ℚ) < 2^p := by positivity
  have u := h.2
  rw [R_def, div_le_div_iff₀ hp hD] at u
  -- u : 3^q * 2^P ≤ B * 2^p
  have key : (2:ℚ)^s * 3^q ≤ 2^p * (2^s - 1) := by
    have : (2:ℚ)^s * 3^q * 2^P ≤ 2^p * (2^s - 1) * 2^P := by nlinarith
    exact le_of_mul_le_mul_right this hD
  have hlt : (3:ℚ)^q < 2^p := by nlinarith
  have hltN : 3^q < 2^p := by exact_mod_cast hlt
  have : ((2^p : ℕ) : ℚ) ≤ ((2^s * (2^p - 3^q) : ℕ) : ℚ) := by
    push_cast [Nat.cast_sub hltN.le]
    nlinarith
  exact_mod_cast this

end Collatz
