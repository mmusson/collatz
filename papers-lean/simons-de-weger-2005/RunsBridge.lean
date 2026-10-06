import RunsRotate
import TwoCircuit
import LinForm
import RunsCert

/-!
# Rotation bridge: few-run cycles are circuits

Closes the **phase gap** of the round-4/5/7 circuit theorems (`one_circuit_eq_one`,
`two_circuit_eq_one`, `no_circuits_of_linForm`), which are stated for sequences starting at
the beginning of an odd run.

* T0: transition lemmas (`runStart_eq_one`, `exists_runStart_between`,
  `exists_runStart_of_oddRuns_pos`, `oddRuns_eq_sum`, `card_le_oddRuns`, `one_circuit_oddSteps`).
* T1: `oddRuns_pos_of_cycle` (a positive cycle has ≥ 1 transition), `rotate_to_run_start`,
  `one_run_bridge`, `few_runs_bridge`: for **any** period `L` (not necessarily minimal) with
  `1 ≤ oddRuns L x ≤ 2`, some rotation `T^[s] x` is an `IsOneCircuit` or `IsTwoCircuit` of
  total length `L`.
* T2: `few_runs_cycle_trivial` (**unconditional**, rotation-free): a positive `T`-cycle point
  with `oddRuns L x ≤ 2` and `S_L(x) < 10^5` is `1` or `2`;
  `few_runs_cycle_trivial_of_linForm` (**CONDITIONAL** on the unformalized `LinFormHyp`): the
  same with no bound on `S_L(x)`; `C`-level corollaries
  `nontrivial_C_cycle_three_runs` and `nontrivial_C_cycle_three_runs_of_linForm`
  ("`LinFormHyp` ⇒ every nontrivial cycle has ≥ 3 odd runs").

About `L`: in every theorem here `L` may be **any** period of `x`, not
necessarily the minimal one.  If `L = t·L₀` with `L₀` the minimal period, then `oddRuns L x` and
`oddSteps L x` are `t` times the per-lap values (`oddRuns_mul`, `oddSteps_mul`), so hypotheses
such as `oddRuns L x ≤ 2` and `S_L(x) < K` refer to the chosen window of length `L`.

Non-vacuity: the only known positive instance of `few_runs_bridge` and
of the circuit predicates is the trivial cycle (`x ∈ {1,2}`); the 2-circuit branch is expected to
be empty, and non-vacuity of the hypotheses is exhibited only via the trivial cycle.  The larger
range `S_L < 10781274` (resp. `225644606`) is in `Farey.lean` (resp. `FareyStretch.lean`).

The unconditional result is a finite instance of Steiner (1977) / Simons (2005);
the conditional one reproduces Steiner + Simons modulo Rhin (1987).  `LinFormHyp` is NOT
proved here and its constants `(100, 14)` have not
been checked against the literature.
-/

namespace Collatz
open CollatzProof

/-! ## T0: transition lemmas -/

theorem runStart_eq_one {z : ℕ} (h : runStart z = 1) : z % 2 = 0 ∧ T z % 2 = 1 := by
  unfold runStart at h
  split_ifs at h with hc
  · exact hc

theorem runStart_of_odd {z : ℕ} (h : z % 2 = 1) : runStart z = 0 := by
  unfold runStart
  simp [h]

theorem runStart_of_even_odd {z : ℕ} (h0 : z % 2 = 0) (h1 : T z % 2 = 1) : runStart z = 1 := by
  unfold runStart
  simp [h0, h1]

/-- Sum formula: `oddRuns j n = ∑_{i<j} runStart (T^i n)`. -/
theorem oddRuns_eq_sum (j n : ℕ) :
    oddRuns j n = ∑ i ∈ Finset.range j, runStart (T^[i] n) := by
  induction j with
  | zero => simp [oddRuns]
  | succ j ih => rw [oddRuns_add j 1 n, oddRuns_one, ih, Finset.sum_range_succ]

/-- A set `S ⊆ [0,j)` of transition indices gives `|S| ≤ oddRuns j n`. -/
theorem card_le_oddRuns {j n : ℕ} (S : Finset ℕ) (hS : ∀ i ∈ S, i < j)
    (h1 : ∀ i ∈ S, runStart (T^[i] n) = 1) : S.card ≤ oddRuns j n := by
  rw [oddRuns_eq_sum, Finset.card_eq_sum_ones]
  calc ∑ i ∈ S, 1 = ∑ i ∈ S, runStart (T^[i] n) := Finset.sum_congr rfl (fun i hi => (h1 i hi).symm)
    _ ≤ ∑ i ∈ Finset.range j, runStart (T^[i] n) :=
        Finset.sum_le_sum_of_subset (fun i hi => Finset.mem_range.mpr (hS i hi))

theorem one_le_oddRuns {j n i : ℕ} (hi : i < j) (h : runStart (T^[i] n) = 1) :
    1 ≤ oddRuns j n := by
  have := card_le_oddRuns (j := j) (n := n) {i} (by simpa using hi) (by simpa using h)
  simpa using this

theorem two_le_oddRuns {j n i1 i2 : ℕ} (h12 : i1 < i2) (hi : i2 < j)
    (h1 : runStart (T^[i1] n) = 1) (h2 : runStart (T^[i2] n) = 1) : 2 ≤ oddRuns j n := by
  have := card_le_oddRuns (j := j) (n := n) {i1, i2}
    (by intro i hi'; simp at hi'; omega)
    (by intro i hi'; simp at hi'; rcases hi' with rfl | rfl <;> assumption)
  rwa [Finset.card_pair h12.ne] at this

theorem three_le_oddRuns {j n i1 i2 i3 : ℕ} (h12 : i1 < i2) (h23 : i2 < i3) (hi : i3 < j)
    (h1 : runStart (T^[i1] n) = 1) (h2 : runStart (T^[i2] n) = 1)
    (h3 : runStart (T^[i3] n) = 1) : 3 ≤ oddRuns j n := by
  have := card_le_oddRuns (j := j) (n := n) {i1, i2, i3}
    (by intro i hi'; simp at hi'; omega)
    (by intro i hi'; simp at hi'; rcases hi' with rfl | rfl | rfl <;> assumption)
  rwa [Finset.card_eq_three.mpr ⟨i1, i2, i3, h12.ne, (h12.trans h23).ne, h23.ne, rfl⟩] at this

/-- Located transition, base-point form. -/
theorem exists_runStart_le (d : ℕ) : ∀ z, z % 2 = 0 → T^[d+1] z % 2 = 1 →
    ∃ i ≤ d, runStart (T^[i] z) = 1 := by
  induction d with
  | zero =>
    intro z hz h1
    exact ⟨0, le_rfl, runStart_of_even_odd hz (by simpa using h1)⟩
  | succ d ih =>
    intro z hz h1
    rcases Nat.mod_two_eq_zero_or_one (T z) with h | h
    · rw [Function.iterate_succ_apply] at h1
      obtain ⟨i, hi, hr⟩ := ih (T z) h h1
      exact ⟨i + 1, by omega, by rwa [Function.iterate_succ_apply]⟩
    · exact ⟨0, by omega, runStart_of_even_odd hz h⟩

/-- **T0(a), located form.** Between an even index `e` and a later odd index `f` there is an
even→odd transition. -/
theorem exists_runStart_between {n e f : ℕ} (hef : e < f) (he : T^[e] n % 2 = 0)
    (hf : T^[f] n % 2 = 1) : ∃ i, e ≤ i ∧ i < f ∧ runStart (T^[i] n) = 1 := by
  have hf' : T^[f - e - 1 + 1] (T^[e] n) % 2 = 1 := by
    rw [iter_shift, show e + (f - e - 1 + 1) = f by omega]; exact hf
  obtain ⟨i, hi, hr⟩ := exists_runStart_le (f - e - 1) _ he hf'
  rw [iter_shift] at hr
  exact ⟨e + i, by omega, by omega, hr⟩

/-- **T0(a), counting form.** -/
theorem oddRuns_pos_of_even_odd (d : ℕ) : ∀ z, 1 ≤ d → z % 2 = 0 → T^[d] z % 2 = 1 →
    1 ≤ oddRuns d z := by
  intro z hd hz h1
  obtain ⟨i, -, hi, hr⟩ := exists_runStart_between (n := z) hd (by simpa using hz) h1
  exact one_le_oddRuns hi hr

/-- **T0(b).** A positive run count is witnessed by a transition index. -/
theorem exists_runStart_of_oddRuns_pos (j : ℕ) : ∀ n, 1 ≤ oddRuns j n →
    ∃ i < j, runStart (T^[i] n) = 1 := by
  induction j with
  | zero => intro n h; simp [oddRuns] at h
  | succ j ih =>
    intro n h
    have e : oddRuns (j+1) n = oddRuns j (T n) + runStart n := rfl
    by_cases hr : runStart n = 1
    · exact ⟨0, by omega, hr⟩
    · have hr0 : runStart n = 0 := by unfold runStart at hr ⊢; split_ifs at hr ⊢ <;> simp_all
      obtain ⟨i, hi, h'⟩ := ih (T n) (by omega)
      exact ⟨i + 1, by omega, by rwa [Function.iterate_succ_apply]⟩

/-- **T0(d).** The orbit of `1` is `{1,2}`. -/
theorem T_iterate_one (j : ℕ) : T^[j] 1 = 1 ∨ T^[j] 1 = 2 := iterate_T_one_mem j

/-- **T0(e).** A 1-circuit `IsOneCircuit m k l` has exactly `k` odd steps per period. -/
theorem one_circuit_oddSteps {m k l : ℕ} (h : IsOneCircuit m k l) : oddSteps (k+l) m = k := by
  obtain ⟨-, -, h1, h2, -⟩ := h
  rw [oddSteps_add, oddSteps_odd_run k m h1,
    oddSteps_even_run l _ (fun i hi => by rw [iter_shift]; exact h2 i hi)]
  omega

/-! ## T1: rotation bridge -/

/-- **T1(i).** A positive `T`-cycle of length `L > 0` has at least one even→odd transition. -/
theorem oddRuns_pos_of_cycle {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) :
    1 ≤ oddRuns L x := by
  rcases Nat.mod_two_eq_zero_or_one x with h0 | h1
  · -- x even: find an odd index
    by_cases hall : ∀ i < L, T^[i] x % 2 = 0
    · have := even_run L x hall
      rw [hc] at this
      have h2 : 1 < 2^L := Nat.one_lt_two_pow hL.ne'
      nlinarith
    · push Not at hall
      obtain ⟨o, ho, hodd⟩ := hall
      have hodd' : T^[o] x % 2 = 1 := by omega
      have ho0 : 0 < o := by
        rcases Nat.eq_zero_or_pos o with rfl | h
        · simp at hodd'; omega
        · exact h
      obtain ⟨i, -, hi, hr⟩ := exists_runStart_between (n := x) ho0 (by simpa using h0) hodd'
      exact one_le_oddRuns (by omega) hr
  · -- x odd: find an even index
    by_cases hall : ∀ i < L, T^[i] x % 2 = 1
    · have := odd_run L x hall
      rw [hc] at this
      have e := Nat.eq_of_mul_eq_mul_right (by omega : 0 < x + 1) this
      have := Nat.pow_lt_pow_left (by norm_num : 2 < 3) hL.ne'
      omega
    · push Not at hall
      obtain ⟨e, he, hev⟩ := hall
      have hev' : T^[e] x % 2 = 0 := by omega
      obtain ⟨i, -, hi, hr⟩ := exists_runStart_between (n := x) he hev' (by rw [hc]; exact h1)
      exact one_le_oddRuns hi hr

/-- **T1(ii).** Rotation to the start of an odd run. -/
theorem rotate_to_run_start {x L : ℕ} (hc : T^[L] x = x) (hr : 1 ≤ oddRuns L x) :
    ∃ s, 1 ≤ L ∧ T^[s] x % 2 = 1 ∧ T^[L] (T^[s] x) = T^[s] x ∧
      T^[L-1] (T^[s] x) % 2 = 0 ∧ oddRuns L (T^[s] x) = oddRuns L x := by
  obtain ⟨i0, hi0, hr0⟩ := exists_runStart_of_oddRuns_pos L x hr
  obtain ⟨he, ho⟩ := runStart_eq_one hr0
  refine ⟨i0 + 1, by omega, ?_, iterate_cycle hc _, ?_, oddRuns_rotate hc _⟩
  · rwa [Function.iterate_succ_apply']
  · rw [iter_shift, show i0 + 1 + (L - 1) = i0 + L by omega, iter_period hc]; exact he

/-- First even index after an odd start. -/
theorem first_even {y M : ℕ} (hy : y % 2 = 1) (hM : 1 ≤ M) (hM1 : T^[M-1] y % 2 = 0) :
    ∃ k, 1 ≤ k ∧ k < M ∧ (∀ i < k, T^[i] y % 2 = 1) ∧ T^[k] y % 2 = 0 := by
  have hex : ∃ j, T^[j] y % 2 = 0 := ⟨M-1, hM1⟩
  refine ⟨Nat.find hex, ?_, ?_, ?_, Nat.find_spec hex⟩
  · by_contra h0
    have : Nat.find hex = 0 := by omega
    have hs := Nat.find_spec hex
    rw [this] at hs; simp at hs; omega
  · have := Nat.find_min' hex hM1; omega
  · intro i hi
    have := Nat.find_min hex hi
    omega

/-- Dichotomy after the first even index `k`: either all of `[k,M)` is even, or there is a
first odd index `j1 ∈ (k, M)`, with `[k, j1)` even. -/
theorem even_block_or_next {y k M : ℕ} (hk : T^[k] y % 2 = 0) :
    (∀ j, k ≤ j → j < M → T^[j] y % 2 = 0) ∨
      ∃ j1, k < j1 ∧ j1 < M ∧ (∀ j, k ≤ j → j < j1 → T^[j] y % 2 = 0) ∧ T^[j1] y % 2 = 1 := by
  by_cases hall : ∀ j, k ≤ j → j < M → T^[j] y % 2 = 0
  · exact Or.inl hall
  · right
    push Not at hall
    have hex : ∃ j, k < j ∧ j < M ∧ T^[j] y % 2 = 1 := by
      obtain ⟨j, hkj, hjM, hj⟩ := hall
      have hne : j ≠ k := by rintro rfl; exact hj hk
      exact ⟨j, by omega, hjM, by omega⟩
    obtain ⟨a1, a2, a3⟩ := Nat.find_spec hex
    refine ⟨Nat.find hex, a1, a2, fun j hkj hj => ?_, a3⟩
    rcases Nat.eq_or_lt_of_le hkj with rfl | hlt
    · exact hk
    · have := Nat.find_min hex hj
      push Not at this
      have := this hlt (by omega)
      omega

/-- The transition at the end of the window: `T^[L-1] y` even and `T^[L] y = y` odd. -/
theorem runStart_last {y L : ℕ} (hL : 1 ≤ L) (hc : T^[L] y = y) (hy : y % 2 = 1)
    (hL1 : T^[L-1] y % 2 = 0) : runStart (T^[L-1] y) = 1 := by
  refine runStart_of_even_odd hL1 ?_
  have e : T (T^[L-1] y) = T^[L-1+1] y := (Function.iterate_succ_apply' T (L-1) y).symm
  rw [e, Nat.sub_add_cancel hL, hc]; exact hy

/-- **T1(iv), phased.** Starting at the beginning of an odd run, with at most two transitions
in the window, the cycle is a 1-circuit or a 2-circuit. -/
theorem few_runs_circuit_of_start {y L : ℕ} (hL : 1 ≤ L) (hy : y % 2 = 1) (hc : T^[L] y = y)
    (hL1 : T^[L-1] y % 2 = 0) (h2 : oddRuns L y ≤ 2) :
    (∃ k l, k + l = L ∧ IsOneCircuit y k l) ∨
      (∃ k1 l1 k2 l2, k1 + l1 + k2 + l2 = L ∧ IsTwoCircuit y k1 l1 k2 l2) := by
  have hlast := runStart_last hL hc hy hL1
  obtain ⟨k, hk1, hkL, hodd, hkev⟩ := first_even hy hL hL1
  rcases even_block_or_next (M := L) hkev with hA | ⟨j1, hkj1, hj1L, hev1, hj1odd⟩
  · left
    refine ⟨k, L - k, by omega, hk1, by omega, hodd, fun i hi => hA _ (by omega) (by omega), ?_⟩
    rw [show k + (L - k) = L by omega]; exact hc
  · right
    have hj1L1 : j1 < L - 1 := by
      rcases Nat.lt_or_ge j1 (L-1) with h | h
      · exact h
      · have : j1 = L - 1 := by omega
        rw [this] at hj1odd; omega
    obtain ⟨i1, hi1a, hi1b, hr1⟩ := exists_runStart_between (n := y) hkj1 hkev hj1odd
    set z := T^[j1] y with hz
    set M := L - j1 with hMdef
    have hM1 : T^[M-1] z % 2 = 0 := by
      rw [hz, iter_shift, show j1 + (M - 1) = L - 1 by omega]; exact hL1
    obtain ⟨k2, hk21, hk2M, hodd2, hk2ev⟩ := first_even hj1odd (by omega) hM1
    rcases even_block_or_next (M := M) hk2ev with hA2 | ⟨j2, hkj2, hj2M, -, hj2odd⟩
    · refine ⟨k, j1 - k, k2, M - k2, by omega, hk1, by omega, hk21, by omega, hodd,
        fun i hi => hev1 _ (by omega) (by omega), fun i hi => ?_, fun i hi => ?_, ?_⟩
      · rw [show k + (j1 - k) + i = j1 + i by omega, ← iter_shift]; exact hodd2 i hi
      · rw [show k + (j1 - k) + k2 + i = j1 + (k2 + i) by omega, ← iter_shift]
        exact hA2 _ (by omega) (by omega)
      · rw [show k + (j1 - k) + k2 + (M - k2) = L by omega]; exact hc
    · exfalso
      have hj2M1 : j2 < M - 1 := by
        rcases Nat.lt_or_ge j2 (M-1) with h | h
        · exact h
        · have : j2 = M - 1 := by omega
          rw [this] at hj2odd; omega
      obtain ⟨i2, hi2a, hi2b, hr2⟩ := exists_runStart_between (n := z) hkj2 hk2ev hj2odd
      rw [hz, iter_shift] at hr2
      have := three_le_oddRuns (n := y) (j := L) (i1 := i1) (i2 := j1 + i2) (i3 := L - 1)
        (by omega) (by omega) (by omega) hr1 hr2 hlast
      omega

/-- **T1(iv).** A `T`-cycle window with 1 or 2 transitions rotates to a 1- or 2-circuit. -/
theorem few_runs_bridge {x L : ℕ} (hc : T^[L] x = x) (h1 : 1 ≤ oddRuns L x)
    (h2 : oddRuns L x ≤ 2) :
    ∃ s, (∃ k l, k + l = L ∧ IsOneCircuit (T^[s] x) k l) ∨
      (∃ k1 l1 k2 l2, k1 + l1 + k2 + l2 = L ∧ IsTwoCircuit (T^[s] x) k1 l1 k2 l2) := by
  obtain ⟨s, hL, hy, hcy, hL1, hrr⟩ := rotate_to_run_start hc h1
  exact ⟨s, few_runs_circuit_of_start hL hy hcy hL1 (by omega)⟩

/-- **T1(iii).** A `T`-cycle window with exactly one transition rotates to a 1-circuit. -/
theorem one_run_bridge {x L : ℕ} (hc : T^[L] x = x) (hr : oddRuns L x = 1) :
    ∃ s k l, k + l = L ∧ IsOneCircuit (T^[s] x) k l := by
  obtain ⟨s, hL, hy, hcy, hL1, hrr⟩ := rotate_to_run_start hc (by omega)
  have hlast := runStart_last hL hcy hy hL1
  obtain ⟨k, hk1, hkL, hodd, hkev⟩ := first_even hy hL hL1
  rcases even_block_or_next (M := L) hkev with hA | ⟨j1, hkj1, hj1L, -, hj1odd⟩
  · refine ⟨s, k, L - k, by omega, hk1, by omega, hodd, fun i hi => hA _ (by omega) (by omega), ?_⟩
    rw [show k + (L - k) = L by omega]; exact hcy
  · exfalso
    have hj1L1 : j1 < L - 1 := by
      rcases Nat.lt_or_ge j1 (L-1) with h | h
      · exact h
      · have : j1 = L - 1 := by omega
        rw [this] at hj1odd; omega
    obtain ⟨i1, -, hi1b, hr1⟩ := exists_runStart_between hkj1 hkev hj1odd
    have := two_le_oddRuns (j := L) (i1 := i1) (i2 := L - 1) (by omega) (by omega) hr1 hlast
    omega

/-- The bridge really rotates: `2 → 1 → 2` is the 1-circuit `IsOneCircuit 1 1 1` after one step. -/
example : ∃ s k l, k + l = 2 ∧ IsOneCircuit (T^[s] 2) k l :=
  one_run_bridge (x := 2) (L := 2) (by decide) (by decide)

/-! ## T2: corollaries for `C`-cycles -/

/-- Recover a cycle point from any rotation of it. -/
theorem exists_back {x L : ℕ} (hL : 0 < L) (hc : T^[L] x = x) (s : ℕ) :
    T^[s * (L - 1)] (T^[s] x) = x := by
  rw [iter_shift]
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [show s + s * (L' + 1 - 1) = s * (L' + 1) by simp; ring]
  exact iterate_mul_cycle hc s

/-- If some rotation of a cycle point is `1`, the point is `1` or `2`. -/
theorem eq_one_or_two_of_rotate {x L s : ℕ} (hL : 0 < L) (hc : T^[L] x = x)
    (h : T^[s] x = 1) : x = 1 ∨ x = 2 := by
  have := exists_back hL hc s
  rw [h] at this
  rw [← this]; exact T_iterate_one _

/-- Shared core: circuit exclusion ⇒ few-run cycle exclusion. -/
theorem few_runs_cycle_trivial_core {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (hr : oddRuns L x ≤ 2)
    (H1 : ∀ m k l, IsOneCircuit m k l → oddSteps (k+l) m = oddSteps L x → m = 1)
    (H2 : ∀ m k1 l1 k2 l2, IsTwoCircuit m k1 l1 k2 l2 →
      oddSteps (k1+l1+k2+l2) m = oddSteps L x → m = 1) : x = 1 ∨ x = 2 := by
  obtain ⟨s, hs⟩ := few_runs_bridge hc (oddRuns_pos_of_cycle hx hL hc) hr
  have hinv := oddSteps_cycle_invariant hc s
  apply eq_one_or_two_of_rotate hL hc (s := s)
  rcases hs with ⟨k, l, hkl, h⟩ | ⟨k1, l1, k2, l2, hkl, h⟩
  · exact H1 _ _ _ h (by rw [hkl, hinv])
  · exact H2 _ _ _ _ _ h (by rw [hkl, hinv])

/-- **T2(a), unconditional and rotation-free.** A point `x > 0` of a `T`-cycle of length
`L > 0` whose window has at most two even→odd transitions and fewer than `100000` odd steps
is `1` or `2`.  (Finite instance of Steiner 1977 / Simons 2005; classical.)  `L` may be any
period (not necessarily minimal); `oddRuns L x`, `oddSteps L x` count the chosen window, i.e.
`t` laps give `t` times the per-lap values.  Improved to `S_L < 10781274` in
`Farey.few_runs_cycle_trivial_farey`. -/
theorem few_runs_cycle_trivial {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (hr : oddRuns L x ≤ 2) (hk : oddSteps L x < 100000) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_core hx hL hc hr
    (fun m k l h e => one_circuit_eq_one h (by rw [one_circuit_oddSteps h] at e; omega))
    (fun m k1 l1 k2 l2 h e => two_circuit_eq_one h (by rw [two_circuit_oddSteps h] at e; omega))

/-- **T2(b), CONDITIONAL** on the unformalized `LinFormHyp K0 c μ` (with `K0 ≤ 100000`,
`8(c+17μ+2) ≤ 2^16`): every positive `T`-cycle point whose window has at most two
even→odd transitions is `1` or `2`.  `L` may be any period (the run count refers to the
chosen window of length `L`). -/
theorem few_runs_cycle_trivial_of_linForm {K0 c μ : ℕ} (hK0 : K0 ≤ 100000)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K0 c μ) {x L : ℕ} (hx : 0 < x)
    (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  have HH := no_circuits_of_linForm hK0 h0 H
  few_runs_cycle_trivial_core hx hL hc hr (fun m k l h _ => HH.1 m k l h)
    (fun m k1 l1 k2 l2 h _ => HH.2 m k1 l1 k2 l2 h)

/-- **T2(b), named instance, CONDITIONAL** on `LinFormHyp 100000 100 14` (unformalized; not
checked against the literature). -/
theorem few_runs_cycle_trivial_of_linForm_100000 (H : LinFormHyp 100000 100 14) {x L : ℕ}
    (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_linForm le_rfl (by norm_num) H hx hL hc hr

/-- **T2(c).** For `C`-cycles: a positive `C`-cycle point `n ∉ {1,2,4}` yields an odd `m`,
`2^17 ≤ m ≤ n`, on a `T`-cycle of length `L > 0`, with `S_L(m) ≥ 971`,
(`S_L(m) ≥ 10^4` or `≥ 54` runs) and (`S_L(m) ≥ 10^5` or `≥ 3` runs). -/
theorem nontrivial_C_cycle_three_runs (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 971 ≤ oddSteps L m ∧
      (10000 ≤ oddSteps L m ∨ 54 ≤ oddRuns L m) ∧
      (100000 ≤ oddSteps L m ∨ 3 ≤ oddRuns L m) := by
  obtain ⟨m, L, a1, a2, a3, a4, a5, a6, a7⟩ := nontrivial_C_cycle_runs n hn ℓ hℓ h h1 h2 h4
  refine ⟨m, L, a1, a2, a3, a4, a5, a6, a7, ?_⟩
  have : (2:ℕ)^17 = 131072 := by norm_num
  by_contra hh
  push Not at hh
  rcases few_runs_cycle_trivial (by omega) a4 a5 (by omega) hh.1 with e | e <;> omega

/-- **T2(c), CONDITIONAL** on the unformalized `LinFormHyp`: every nontrivial `C`-cycle
yields a `T`-cycle point `m ≥ 2^17` whose window has at least 3 even→odd transitions. -/
theorem nontrivial_C_cycle_three_runs_of_linForm {K0 c μ : ℕ} (hK0 : K0 ≤ 100000)
    (h0 : 8 * (c + 17*μ + 2) ≤ 2^16) (H : LinFormHyp K0 c μ) (n : ℕ) (hn : 0 < n) (ℓ : ℕ)
    (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 3 ≤ oddRuns L m := by
  obtain ⟨m, L, a1, a2, a3, a4, a5, -, -⟩ := nontrivial_C_cycle_runs n hn ℓ hℓ h h1 h2 h4
  refine ⟨m, L, a1, a2, a3, a4, a5, ?_⟩
  have : (2:ℕ)^17 = 131072 := by norm_num
  by_contra hh
  rcases few_runs_cycle_trivial_of_linForm hK0 h0 H (by omega) a4 a5 (by omega) with e | e <;>
    omega

/-- Non-vacuity of T2(a)'s hypotheses: the trivial cycle `1 → 2 → 1`. -/
example : 0 < 1 ∧ 0 < 2 ∧ T^[2] 1 = 1 ∧ oddRuns 2 1 ≤ 2 ∧ oddSteps 2 1 < 100000 := by decide

end Collatz

#print axioms Collatz.oddRuns_eq_sum
#print axioms Collatz.exists_runStart_between
#print axioms Collatz.exists_runStart_of_oddRuns_pos
#print axioms Collatz.one_circuit_oddSteps
#print axioms Collatz.oddRuns_pos_of_cycle
#print axioms Collatz.rotate_to_run_start
#print axioms Collatz.one_run_bridge
#print axioms Collatz.few_runs_bridge
#print axioms Collatz.few_runs_cycle_trivial
#print axioms Collatz.few_runs_cycle_trivial_of_linForm
#print axioms Collatz.few_runs_cycle_trivial_of_linForm_100000
#print axioms Collatz.nontrivial_C_cycle_three_runs
#print axioms Collatz.nontrivial_C_cycle_three_runs_of_linForm
