/-
Copyright (c) 2026 Michael Musson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Musson
-/
import FareyBig

/-!
# A run lower bound growing with the number of odd steps

In this file we prove that the odd orbit minimum `m` of a `T`-cycle with `k` odd steps and `r` odd
runs satisfies `r ≥ 256` or `3·5^r·k < 890·8^r`, i.e. `r > log_{8/5}(3k/890)`, whenever
`k < K1big ≈ 3.15·10^50`. This follows from the Simons–de Weger bound `runs_bound_of_min` with the
gap exponent `170` of `gapBelow_K1big` and the identity `3 W(r) + 5^r = 8^r`. No lower bound on `m`
is needed. For instance, cycles with `10^11 ≤ k < K1big` have at least `42` odd runs, and the rung
"at least `29` runs, or `k < 225644606`, or `k ≥ K1big`" of `runs_ge_29_K1big` follows.

We also give a pointwise version of the gap interface for `TwoCircHyp`, replacing the cap
`s ≤ 20000` of `twoCirc_of_gap_s` by the condition `3s ≤ ⌊k/2⌋`. The result
`twoCircHyp_of_tail_gap_fun` assumes, as a hypothesis, a `k`-dependent gap for all `k ≥ K1`; this
hypothesis is not proved here.

## Main results

- `three_W_add`: `3 W(r) + 5^r = 8^r`.
- `runs_log_bound`: for the odd orbit minimum `m` of a `T`-cycle with `k = S_L(m) < K1big` and
  `r = oddRuns L m`, `r ≥ 256` or `3·5^r·k < 890·8^r`.
- `runs_ge_of_threshold`: if `a < 256` and `890·8^a ≤ 3·5^a·K`, then `K ≤ S_L(m) < K1big` forces
  more than `a` odd runs.
- `runs_ge_42`, `runs_ge_62`, `runs_ge_86`, `runs_ge_135`, `runs_ge_184`, `runs_ge_233`: the
  instances `k ≥ 10^11, 10^15, 10^20, 10^30, 10^40, 10^50` (each sharp for this inequality).
- `state_of_the_art_runs_log`, `nontrivial_C_cycle_runs_ge_42`: the corresponding statements for
  cycles of the Collatz map `C`.
- `twoCirc_of_gap_pt`, `twoCirc_of_gap_sk`: the `TwoCircHyp` inequality at `k` from a pointwise
  gap.
- `twoCircHyp_of_tail_gap_fun`: `TwoCircHyp 100000` from `GapBelow K1 s` and a `k`-dependent gap
  for `k ≥ K1`.
- `runs_ge_29_of_log`: `oddRuns L m ≥ 29` or `S_L(m) < 225644606` or `S_L(m) ≥ K1big`.

## References

- J. L. Simons, B. M. M. de Weger, *Theoretical and computational bounds for m-cycles of the
  3n+1-problem*, Acta Arith. 117 (2005), 51–70.
- C. Hercher, *There are no Collatz m-cycles with m ≤ 91*, J. Integer Seq. 26 (2023),
  Art. 23.3.5.
-/

namespace Collatz
open CollatzProof

/-! ### The logarithmic run bound -/

/-- `3 W(r) + 5^r = 8^r` (so `W r = (8^r − 5^r)/3`). -/
theorem three_W_add (r : ℕ) : 3 * W r + 5^r = 8^r := by
  induction r with
  | zero => simp [W]
  | succ r ih => simp only [W, pow_succ]; nlinarith [ih]

/-- **Logarithmic run bound.** Let `m` be odd and minimal on its `T`-orbit, `L > 0`,
`T^[L] m = m`, `k = S_L(m) < K1big` and `r = oddRuns L m`. Then `r ≥ 256` or
`3·5^r·k < 890·8^r`, i.e. `r > log_{8/5}(3k/890)`. At `k = 225644606` this already forces
`r ≥ 29`. -/
theorem runs_log_bound {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (hK : oddSteps L m < K1big) :
    256 ≤ oddRuns L m ∨ 3 * 5^(oddRuns L m) * oddSteps L m < 890 * 8^(oddRuns L m) := by
  rcases Nat.lt_or_ge (oddRuns L m) 256 with hr | hr
  · right
    have hm0 : 0 < m := by omega
    have h3 := three_pow_lt_two_pow_of_cycle hm0 hL hc
    have hk0 := oddSteps_pos_of_cycle hm0 hL hc
    have gap := gapBelow_K1big _ L hk0 hK h3
    have rb := runs_bound_of_min (s := 170) (t := 8) hodd hL hc hmin h3 gap
      (le_trans (by omega : oddRuns L m ≤ 256) (by norm_num))
    have hW := three_W_add (oddRuns L m)
    generalize oddRuns L m = r at rb hW
    generalize oddSteps L m = k at rb
    have h5 : 0 < 5^r := by positivity
    norm_num at rb
    nlinarith
  · exact Or.inl hr

/-- Threshold arithmetic: if `890·8^a ≤ 3·5^a·K`, `K ≤ k` and `3·5^r·k < 890·8^r`, then
`a < r`. -/
theorem lt_of_threshold {a K k r : ℕ} (hth : 890 * 8^a ≤ 3 * 5^a * K) (hk : K ≤ k)
    (hb : 3 * 5^r * k < 890 * 8^r) : a < r := by
  by_contra hcon
  push Not at hcon
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hcon
  have h85 : 5^d ≤ 8^d := Nat.pow_le_pow_left (by norm_num) d
  have hd : 0 < 5^d := by positivity
  rw [pow_add, pow_add] at hth
  have e1 : 3 * (5^r * 5^d) * K ≤ 3 * 5^r * k * 5^d := by
    have := Nat.mul_le_mul_left (3 * 5^r * 5^d) hk
    calc 3 * (5^r * 5^d) * K = 3 * 5^r * 5^d * K := by ring
      _ ≤ 3 * 5^r * 5^d * k := this
      _ = 3 * 5^r * k * 5^d := by ring
  have e2 : 3 * 5^r * k * 5^d < 890 * 8^r * 5^d := Nat.mul_lt_mul_of_pos_right hb hd
  have e3 : 890 * 8^r * 5^d ≤ 890 * (8^r * 8^d) := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_left _ h85
  omega

/-- For every threshold pair `(a, K)` with `a < 256` and `890·8^a ≤ 3·5^a·K`, the odd orbit
minimum `m` of a `T`-cycle with `K ≤ S_L(m) < K1big` has more than `a` odd runs. -/
theorem runs_ge_of_threshold {m L a K : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m)
    (hL : 0 < L) (hc : T^[L] m = m) (ha : a < 256) (hth : 890 * 8^a ≤ 3 * 5^a * K)
    (hKk : K ≤ oddSteps L m) (hK : oddSteps L m < K1big) : a < oddRuns L m := by
  rcases runs_log_bound hodd hmin hL hc hK with h | h
  · omega
  · exact lt_of_threshold hth hKk h

/-- The odd orbit minimum `m` of a `T`-cycle with `10^11 ≤ S_L(m) < K1big` has
`oddRuns L m ≥ 42`. -/
theorem runs_ge_42 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^11 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    42 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 41) (K := 10^11) (by norm_num) (by norm_num) h hK

/-- The odd orbit minimum `m` of a `T`-cycle with `10^15 ≤ S_L(m) < K1big` has
`oddRuns L m ≥ 62`. -/
theorem runs_ge_62 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^15 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    62 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 61) (K := 10^15) (by norm_num) (by norm_num) h hK

/-- The odd orbit minimum `m` of a `T`-cycle with `10^20 ≤ S_L(m) < K1big` has
`oddRuns L m ≥ 86`. -/
theorem runs_ge_86 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^20 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    86 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 85) (K := 10^20) (by norm_num) (by norm_num) h hK

/-- The odd orbit minimum `m` of a `T`-cycle with `10^30 ≤ S_L(m) < K1big` has
`oddRuns L m ≥ 135`. -/
theorem runs_ge_135 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^30 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    135 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 134) (K := 10^30) (by norm_num) (by norm_num) h hK

/-- The odd orbit minimum `m` of a `T`-cycle with `10^40 ≤ S_L(m) < K1big` has
`oddRuns L m ≥ 184`. -/
theorem runs_ge_184 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^40 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    184 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 183) (K := 10^40) (by norm_num) (by norm_num) h hK

/-- The odd orbit minimum `m` of a `T`-cycle with `10^50 ≤ S_L(m) < K1big` has
`oddRuns L m ≥ 233`. -/
theorem runs_ge_233 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^50 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    233 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 232) (K := 10^50) (by norm_num) (by norm_num) h hK

/-! ### Cycles of the Collatz map -/

/-- A positive `C`-cycle point `n ∉ {1, 2, 4}` yields the odd `T`-orbit minimum `m` with
`2^24 ≤ m ≤ n` and minimal period `P`, satisfying the bounds of
`state_of_the_art_runs_minimalPeriod_K1big` and in addition `S_P(m) ≥ K1big` or
`oddRuns P m ≥ 256` or `3·5^r·S_P(m) < 890·8^r`, where `r = oddRuns P m`. -/
theorem state_of_the_art_runs_log (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ (∀ j, m ≤ T^[j] m) ∧
      0 < Function.minimalPeriod T m ∧ T^[Function.minimalPeriod T m] m = m ∧
      (18 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        K1big ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      (29 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        oddSteps (Function.minimalPeriod T m) m < 225644606 ∨
        K1big ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      (62 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        190537 ≤ oddSteps (Function.minimalPeriod T m) m) ∧
      (K1big ≤ oddSteps (Function.minimalPeriod T m) m ∨
        256 ≤ oddRuns (Function.minimalPeriod T m) m ∨
        3 * 5^(oddRuns (Function.minimalPeriod T m) m) *
            oddSteps (Function.minimalPeriod T m) m <
          890 * 8^(oddRuns (Function.minimalPeriod T m) m)) := by
  obtain ⟨m, h1, h2, h3, h6, hP, hPc, b1, b2, b3⟩ :=
    state_of_the_art_runs_minimalPeriod_K1big n hn ℓ hℓ h hne
  refine ⟨m, h1, h2, h3, h6, hP, hPc, b1, b2, b3, ?_⟩
  rcases Nat.lt_or_ge (oddSteps (Function.minimalPeriod T m) m) K1big with hk | hk
  · exact Or.inr (runs_log_bound h1 h6 hP hPc hk)
  · exact Or.inl hk

/-- Every nontrivial `C`-cycle has an odd orbit minimum `m` with `2^24 ≤ m ≤ n` whose per-lap
odd-step count `k` satisfies: if `10^11 ≤ k < K1big`, then `m` has at least `42` odd runs per
lap. -/
theorem nontrivial_C_cycle_runs_ge_42 (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < Function.minimalPeriod T m ∧
      T^[Function.minimalPeriod T m] m = m ∧
      (10^11 ≤ oddSteps (Function.minimalPeriod T m) m →
        oddSteps (Function.minimalPeriod T m) m < K1big →
        42 ≤ oddRuns (Function.minimalPeriod T m) m) := by
  obtain ⟨m, h1, h2, h3, h6, hP, hPc, -⟩ :=
    state_of_the_art_runs_minimalPeriod_K1big n hn ℓ hℓ h hne
  exact ⟨m, h1, h2, h3, hP, hPc, fun a b ↦ runs_ge_42 h1 h6 hP hPc a b⟩

/-! ### A pointwise gap interface for `TwoCircHyp` -/

/-- `3s ≤ h ⇒ 2^s·3^h ≤ 4^h` (since `2·27 = 54 ≤ 64`). -/
theorem pow_gap_absorb {s h : ℕ} (hs : 3 * s ≤ h) : 2^s * 3^h ≤ 4^h := by
  obtain ⟨j, e, he, rfl⟩ : ∃ j e, e < 3 ∧ h = 3 * j + e :=
    ⟨h / 3, h % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod h 3).symm⟩
  have hsj : s ≤ j := by omega
  calc 2^s * 3^(3*j+e) ≤ 2^j * 3^(3*j+e) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hsj)
    _ = 54^j * 3^e := by
        rw [pow_add, pow_mul]; rw [show (54:ℕ) = 2 * 3^3 by norm_num, mul_pow]; ring
    _ ≤ 64^j * 4^e :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) j) (Nat.pow_le_pow_left (by norm_num) e)
    _ = 4^(3*j+e) := by rw [pow_add, pow_mul]; norm_num

/-- Pointwise gap version of `twoCirc_of_gap_s`: a single gap `2^L ≤ 2^s(2^L − 3^k)` at
`k ≥ 10^5` with `2^s·3^{⌊k/2⌋} ≤ 4^{⌊k/2⌋}` gives the `TwoCircHyp` inequality at `k`. -/
theorem twoCirc_of_gap_pt {s k L : ℕ} (hk : 100000 ≤ k)
    (hgap : 2^L ≤ 2^s * (2^L - 3^k)) (hs : 2^s * 3^(k/2) ≤ 4^(k/2)) :
    2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k) := by
  set h := k / 2 with hh
  have h2h : 2 * h ≤ k := Nat.mul_div_le k 2
  have s1 : 2^(h+1) + 3^h ≤ 2 * 3^h := by
    have := two_pow_succ_le_three_pow (h := h) (by omega); omega
  have s3 : 4^h ≤ 2^k := by
    rw [show (4:ℕ) = 2^2 by norm_num, ← pow_mul]; exact Nat.pow_le_pow_right (by norm_num) h2h
  have s4 : 2^s * (2^(h+1) + 3^h) ≤ 2^(k+1) := by
    calc 2^s * (2^(h+1) + 3^h) ≤ 2^s * (2 * 3^h) := Nat.mul_le_mul_left _ s1
      _ = 2 * (2^s * 3^h) := by ring
      _ ≤ 2 * 2^k := Nat.mul_le_mul_left _ (hs.trans s3)
      _ = 2^(k+1) := by ring
  set S := 2^(h+1) + 3^h
  set D := 2^L - 3^k
  have h30 : 0 < 2^s := by positivity
  apply Nat.le_of_mul_le_mul_left _ h30
  calc 2^s * (2^L * S) = 2^L * (2^s * S) := by ring
    _ ≤ 2^L * 2^(k+1) := Nat.mul_le_mul_left _ s4
    _ ≤ (2^s * D) * 2^(k+1) := Nat.mul_le_mul_right _ hgap
    _ = 2^s * (2^(k+1) * D) := by ring

/-- `GapBelow K1 s`, `3s ≤ ⌊k/2⌋`, `10^5 ≤ k < K1` and `3^k < 2^L` give the `TwoCircHyp`
inequality at `k`. The cap `s ≤ 20000` of `twoCirc_of_gap_s` is replaced by the pointwise
condition `3s ≤ ⌊k/2⌋`. -/
theorem twoCirc_of_gap_sk {K1 s k L : ℕ} (hG : GapBelow K1 s) (hs : 3 * s ≤ k / 2)
    (hk : 100000 ≤ k) (hK : k < K1) (hL : 3^k < 2^L) :
    2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k) :=
  twoCirc_of_gap_pt hk (hG k L (by omega) hK hL) (pow_gap_absorb hs)

/-- If `GapBelow K1 s` holds with `s ≤ 20000` and, for `k ≥ K1`, a `k`-dependent gap
`2^L ≤ 2^{sf k}(2^L − 3^k)` with `3·sf k ≤ ⌊k/2⌋` holds (for example a gap of size `(log k)^2`
as given by lower bounds for linear forms in two logarithms), then `TwoCircHyp 100000`. -/
theorem twoCircHyp_of_tail_gap_fun {K1 s : ℕ} (sf : ℕ → ℕ) (hG : GapBelow K1 s)
    (hs : s ≤ 20000)
    (htail : ∀ k L, K1 ≤ k → 3^k < 2^L → 2^L ≤ 2^(sf k) * (2^L - 3^k))
    (hsf : ∀ k, K1 ≤ k → 3 * sf k ≤ k / 2) : TwoCircHyp 100000 := by
  intro k L hk hL
  rcases Nat.lt_or_ge k K1 with hK | hK
  · exact twoCirc_of_gap_s hG hs hk hK hL
  · exact twoCirc_of_gap_pt hk (htail k L hK hL) (pow_gap_absorb (hsf k hK))

/-! ### The fixed rung of `runs_ge_29_K1big` -/

/-- For the odd orbit minimum `m` of a `T`-cycle with `L > 0`: `oddRuns L m ≥ 29` or
`S_L(m) < 225644606` or `S_L(m) ≥ K1big`. This is `runs_ge_29_K1big` without the hypothesis
`2^24 ≤ m`. -/
theorem runs_ge_29_of_log {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m)
    (hL : 0 < L) (hc : T^[L] m = m) :
    29 ≤ oddRuns L m ∨ oddSteps L m < 225644606 ∨ K1big ≤ oddSteps L m := by
  by_cases h1 : oddSteps L m < 225644606
  · exact Or.inr (Or.inl h1)
  by_cases h2 : K1big ≤ oddSteps L m
  · exact Or.inr (Or.inr h2)
  left
  have := runs_ge_of_threshold (a := 28) (K := 225644606) hodd hmin hL hc (by norm_num)
    (by norm_num) (by omega) (Nat.lt_of_not_le h2)
  omega

/-! ### Examples -/

-- The logarithmic bound is consistent on the trivial cycle (`k = r = 1`).
example : 3 * 5^(oddRuns 2 1) * oddSteps 2 1 < 890 * 8^(oddRuns 2 1) := by decide

-- The threshold inequality used for `runs_ge_29_of_log` fails at `a = 29`, `K = 225644606`.
example : ¬ (890 * 8^29 ≤ 3 * 5^29 * 225644606) := by norm_num

end Collatz
