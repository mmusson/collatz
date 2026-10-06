import FareyBig

/-!
# `k`-dependent run lower bound up to `K1big`; pointwise-gap `TwoCircHyp` interface

* **T1 (unconditional, CLASSICAL).** `runs_log_bound`: for the odd orbit-minimum `m` of a
  `T`-cycle (any period `L > 0`) with `k = S_L(m) < K1big ≈ 3.15·10^50` and `r = oddRuns L m`:
  `r ≥ 256` or `3·5^r·k < 890·8^r`, i.e. `r > log_{8/5}(3k/890)`. Corollaries `runs_ge_42`
  (`k ≥ 10^11`), `runs_ge_62` (`10^15`), `runs_ge_86` (`10^20`), `runs_ge_135` (`10^30`),
  `runs_ge_184` (`10^40`), `runs_ge_233` (`10^50`), each for `k < K1big` (all thresholds sharp
  for this inequality: `a+1` fails at the same `K`). C-level `state_of_the_art_runs_log`.
  The fixed rung "≥ 29 runs or `k < 225644606` or `k ≥ K1big`" of `runs_bounds_big` is
  recovered as the theorem `runs_ge_29_of_log`, which does not need `2^24 ≤ m`. Newly excluded (unconditionally, relative to this library): e.g. cycles with
  `29..41` odd runs and `10^11 ≤ k < K1big`.
* **T2 (supporting infrastructure; `twoCircHyp_of_tail_gap_fun` is CONDITIONAL).**
  `twoCirc_of_gap_pt` / `twoCirc_of_gap_sk` replace the cap `s ≤ 20000` of `twoCirc_of_gap_s` by
  the pointwise condition `3s ≤ ⌊k/2⌋`.

A classical finite-range instance of Simons–de Weger 2005 (Hercher 2023 excludes all
cycles with `≤ 91` odd runs, for all `k`).
-/

namespace Collatz
open CollatzProof

/-- `3 W(r) + 5^r = 8^r` (so `W r = (8^r − 5^r)/3`). -/
theorem three_W_add (r : ℕ) : 3 * W r + 5^r = 8^r := by
  induction r with
  | zero => simp [W]
  | succ r ih => simp only [W, pow_succ]; nlinarith [ih]

/-- **Unconditional, CLASSICAL (finite-range instance of Simons–de Weger 2005).** Let `m` be odd and minimal on its `T`-orbit, `L > 0`, `T^[L] m = m`,
`k = S_L(m) < K1big`, `r = oddRuns L m`. Then `r ≥ 256` or `3·5^r·k < 890·8^r`, i.e.
`r > log_{8/5}(3k/890)`. (From `runs_bound_of_min` with `s = 170` (`gapBelow_big`), `t = 8`,
and `3W(r) + 5^r = 8^r`.) Strictly strengthens the fixed rung of `runs_bounds_big`: at
`k = 225644606` it already forces `r ≥ 29`, and the bound grows like `log_{1.6} k`. No lower
bound on `m` is needed. -/
theorem runs_log_bound {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (hK : oddSteps L m < K1big) :
    256 ≤ oddRuns L m ∨ 3 * 5^(oddRuns L m) * oddSteps L m < 890 * 8^(oddRuns L m) := by
  rcases Nat.lt_or_ge (oddRuns L m) 256 with hr | hr
  · right
    have hm0 : 0 < m := by omega
    have h3 := three_pow_lt_two_pow_of_cycle hm0 hL hc
    have hk0 := oddSteps_pos_of_cycle hm0 hL hc
    have gap := gapBelow_big _ L hk0 hK h3
    have rb := runs_bound_of_min (s := 170) (t := 8) hodd hL hc hmin h3 gap
      (le_trans (by omega : oddRuns L m ≤ 256) (by norm_num))
    have hW := three_W_add (oddRuns L m)
    generalize oddRuns L m = r at rb hW
    generalize oddSteps L m = k at rb
    have h5 : 0 < 5^r := by positivity
    norm_num at rb
    nlinarith
  · exact Or.inl hr

/-- Threshold arithmetic: if `890·8^a ≤ 3·5^a·K`, `K ≤ k` and `3·5^r·k < 890·8^r` then `a < r`. -/
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


/-- **Unconditional, classical.** For every threshold pair `(a, K)` with `a < 256` and
`890·8^a ≤ 3·5^a·K`: the odd orbit-minimum `m` of a `T`-cycle with `K ≤ S_L(m) < K1big` has
more than `a` odd runs. -/
theorem runs_ge_of_threshold {m L a K : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m)
    (hL : 0 < L) (hc : T^[L] m = m) (ha : a < 256) (hth : 890 * 8^a ≤ 3 * 5^a * K)
    (hKk : K ≤ oddSteps L m) (hK : oddSteps L m < K1big) : a < oddRuns L m := by
  rcases runs_log_bound hodd hmin hL hc hK with h | h
  · omega
  · exact lt_of_threshold hth hKk h

/-- **Unconditional, classical.** Odd orbit-minimum `m` of a `T`-cycle with
`10^11 ≤ S_L(m) < K1big` has `oddRuns L m ≥ 42`. -/
theorem runs_ge_42 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^11 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    42 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 41) (K := 10^11) (by norm_num) (by norm_num) h hK

/-- **Unconditional, classical.** Odd orbit-minimum `m` of a `T`-cycle with
`10^15 ≤ S_L(m) < K1big` has `oddRuns L m ≥ 62`. -/
theorem runs_ge_62 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^15 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    62 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 61) (K := 10^15) (by norm_num) (by norm_num) h hK

/-- **Unconditional, classical.** Odd orbit-minimum `m` of a `T`-cycle with
`10^20 ≤ S_L(m) < K1big` has `oddRuns L m ≥ 86`. -/
theorem runs_ge_86 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^20 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    86 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 85) (K := 10^20) (by norm_num) (by norm_num) h hK

/-- **Unconditional, classical.** Odd orbit-minimum `m` of a `T`-cycle with
`10^30 ≤ S_L(m) < K1big` has `oddRuns L m ≥ 135`. -/
theorem runs_ge_135 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^30 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    135 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 134) (K := 10^30) (by norm_num) (by norm_num) h hK

/-- **Unconditional, classical.** Odd orbit-minimum `m` of a `T`-cycle with
`10^40 ≤ S_L(m) < K1big` has `oddRuns L m ≥ 184`. -/
theorem runs_ge_184 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^40 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    184 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 183) (K := 10^40) (by norm_num) (by norm_num) h hK

/-- **Unconditional, classical.** Odd orbit-minimum `m` of a `T`-cycle with
`10^50 ≤ S_L(m) < K1big` has `oddRuns L m ≥ 233`. -/
theorem runs_ge_233 {m L : ℕ} (hodd : m % 2 = 1) (hmin : ∀ j, m ≤ T^[j] m) (hL : 0 < L)
    (hc : T^[L] m = m) (h : 10^50 ≤ oddSteps L m) (hK : oddSteps L m < K1big) :
    233 ≤ oddRuns L m :=
  runs_ge_of_threshold hodd hmin hL hc (a := 232) (K := 10^50) (by norm_num) (by norm_num) h hK

/-- **Unconditional, per lap, CLASSICAL (Simons–de Weger-type finite-range instance).** A positive `C`-cycle point `n ∉ {1,2,4}` yields the odd
`T`-orbit minimum `m`, `2^24 ≤ m ≤ n`, `P = minimalPeriod T m`, with the conjuncts of
`state_of_the_art_runs_minimalPeriod_big` and in addition
(`S_P(m) ≥ K1big` or `oddRuns P m ≥ 256` or `3·5^r·S_P(m) < 890·8^r`, `r = oddRuns P m`). -/
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
        3 * 5^(oddRuns (Function.minimalPeriod T m) m) * oddSteps (Function.minimalPeriod T m) m
          < 890 * 8^(oddRuns (Function.minimalPeriod T m) m)) := by
  obtain ⟨m, h1, h2, h3, h6, hP, hPc, b1, b2, b3⟩ :=
    state_of_the_art_runs_minimalPeriod_big n hn ℓ hℓ h hne
  refine ⟨m, h1, h2, h3, h6, hP, hPc, b1, b2, b3, ?_⟩
  rcases Nat.lt_or_ge (oddSteps (Function.minimalPeriod T m) m) K1big with hk | hk
  · exact Or.inr (runs_log_bound h1 h6 hP hPc hk)
  · exact Or.inl hk

/-- **Unconditional, C-level.** Every nontrivial `C`-cycle has an odd orbit-minimum `m`
(`2^24 ≤ m ≤ n`) whose per-lap odd-step count `k` satisfies: if `10^11 ≤ k < K1big` then
`m` has `≥ 42` odd runs per lap (newly excluded: `29..41` runs with `10^11 ≤ k < K1big`). -/
theorem nontrivial_C_cycle_runs_ge_42 (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) :
    ∃ m, m % 2 = 1 ∧ 2^24 ≤ m ∧ m ≤ n ∧ 0 < Function.minimalPeriod T m ∧
      T^[Function.minimalPeriod T m] m = m ∧
      (10^11 ≤ oddSteps (Function.minimalPeriod T m) m →
        oddSteps (Function.minimalPeriod T m) m < K1big →
        42 ≤ oddRuns (Function.minimalPeriod T m) m) := by
  obtain ⟨m, h1, h2, h3, h6, hP, hPc, -⟩ :=
    state_of_the_art_runs_minimalPeriod_big n hn ℓ hℓ h hne
  exact ⟨m, h1, h2, h3, hP, hPc, fun a b => runs_ge_42 h1 h6 hP hPc a b⟩

/-- Non-vacuity / sanity: the bound is consistent on the trivial cycle (`k = r = 1`). -/
example : 3 * 5^(oddRuns 2 1) * oddSteps 2 1 < 890 * 8^(oddRuns 2 1) := by decide

/-! ## T2: pointwise-gap interface -/

/-- `3s ≤ h ⇒ 2^s·3^h ≤ 4^h` (since `2·27 = 54 ≤ 64`). -/
theorem pow_gap_absorb {s h : ℕ} (hs : 3 * s ≤ h) : 2^s * 3^h ≤ 4^h := by
  obtain ⟨j, e, he, rfl⟩ : ∃ j e, e < 3 ∧ h = 3 * j + e := ⟨h / 3, h % 3, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod h 3).symm⟩
  have hsj : s ≤ j := by omega
  calc 2^s * 3^(3*j+e) ≤ 2^j * 3^(3*j+e) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by norm_num) hsj)
    _ = 54^j * 3^e := by rw [pow_add, pow_mul]; rw [show (54:ℕ) = 2 * 3^3 by norm_num, mul_pow]; ring
    _ ≤ 64^j * 4^e := Nat.mul_le_mul (Nat.pow_le_pow_left (by norm_num) j) (Nat.pow_le_pow_left (by norm_num) e)
    _ = 4^(3*j+e) := by rw [pow_add, pow_mul]; norm_num

/-- **Supporting infrastructure (T2).** Pointwise gap version of `twoCirc_of_gap_s`: a single
gap `2^L ≤ 2^s(2^L − 3^k)` at `k ≥ 10^5` with `2^s·3^{⌊k/2⌋} ≤ 4^{⌊k/2⌋}` gives the
`TwoCircHyp` inequality at `k`. No `s ≤ 20000` cap. -/
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

/-- **Supporting infrastructure (T2).** `GapBelow K1 s`, `3s ≤ ⌊k/2⌋`, `10^5 ≤ k < K1`,
`3^k < 2^L` give the `TwoCircHyp` inequality at `k` (the cap `s ≤ 20000` of `twoCirc_of_gap_s`
is replaced by the pointwise condition `3s ≤ ⌊k/2⌋`, i.e. `s` up to about `k/6`). -/
theorem twoCirc_of_gap_sk {K1 s k L : ℕ} (hG : GapBelow K1 s) (hs : 3 * s ≤ k / 2)
    (hk : 100000 ≤ k) (hK : k < K1) (hL : 3^k < 2^L) :
    2^L * (2^(k/2+1) + 3^(k/2)) ≤ 2^(k+1) * (2^L - 3^k) :=
  twoCirc_of_gap_pt hk (hG k L (by omega) hK hL) (pow_gap_absorb hs)

/-- **CONDITIONAL interface** (T2 of `RunsLog`; the tail hypothesis is not discharged here). If
`GapBelow K1 s` (`s ≤ 20000`) holds and, for `k ≥ K1`, a `k`-dependent gap
`2^L ≤ 2^{sf k}(2^L − 3^k)` with `3·sf k ≤ ⌊k/2⌋` holds (e.g. an LMN-type `(log k)^2` gap,
far below `k/6`), then `TwoCircHyp 100000`. Removes the artificial cap `s ≤ 20000`. The tail
hypothesis `htail` is NOT proved here. -/
theorem twoCircHyp_of_tail_gap_fun {K1 s : ℕ} (sf : ℕ → ℕ) (hG : GapBelow K1 s)
    (hs : s ≤ 20000)
    (htail : ∀ k L, K1 ≤ k → 3^k < 2^L → 2^L ≤ 2^(sf k) * (2^L - 3^k))
    (hsf : ∀ k, K1 ≤ k → 3 * sf k ≤ k / 2) : TwoCircHyp 100000 := by
  intro k L hk hL
  rcases Nat.lt_or_ge k K1 with hK | hK
  · exact twoCirc_of_gap_s hG hs hk hK hL
  · exact twoCirc_of_gap_pt hk (htail k L hK hL) (pow_gap_absorb (hsf k hK))

/-! ## explicit subsumption of the fixed rung of `runs_bounds_big` -/

/-- **Unconditional, classical (see `Summary`).** For the odd orbit-minimum `m` of a
`T`-cycle (`L > 0`): `oddRuns L m ≥ 29` or `S_L(m) < 225644606` or `S_L(m) ≥ K1big`. This is the
first conjunct of `runs_bounds_big`, obtained from `runs_ge_of_threshold` (`a = 28`,
`K = 225644606`), with no lower bound `2^24 ≤ m` needed. This makes the `RunsLog` docstring claim
(that the log bound covers that rung) a theorem. -/
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

/-- Sharpness of the threshold inequality used above: `a = 29` fails at `K = 225644606`. -/
example : ¬ (890 * 8^29 ≤ 3 * 5^29 * 225644606) := by norm_num

end Collatz

#print axioms Collatz.three_W_add
#print axioms Collatz.runs_log_bound
#print axioms Collatz.lt_of_threshold
#print axioms Collatz.runs_ge_of_threshold
#print axioms Collatz.runs_ge_42
#print axioms Collatz.runs_ge_62
#print axioms Collatz.runs_ge_86
#print axioms Collatz.runs_ge_135
#print axioms Collatz.runs_ge_184
#print axioms Collatz.runs_ge_233
#print axioms Collatz.state_of_the_art_runs_log
#print axioms Collatz.nontrivial_C_cycle_runs_ge_42
#print axioms Collatz.pow_gap_absorb
#print axioms Collatz.twoCirc_of_gap_pt
#print axioms Collatz.twoCirc_of_gap_sk
#print axioms Collatz.twoCircHyp_of_tail_gap_fun
#print axioms Collatz.runs_ge_29_of_log
