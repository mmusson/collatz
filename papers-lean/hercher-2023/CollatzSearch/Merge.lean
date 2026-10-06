import CollatzSearch.RunGrowth
import CollatzSearch.Sieve24
import Mathlib.Tactic

/-!
# Hercher's merge lemma (Hercher 2023, arXiv:2201.00406, Lemma 9 and Remark 10)

CLASSICAL (Hercher 2023). NOT progress on `no_nontrivial_cycles`, which remains OPEN.

All statements are about the accelerated map `T` (`n/2` on evens, `(3n+1)/2` on odds).

* `merge_step`: if `n + 1 = 2^k b` (`k ≥ 1`, `b` odd) and `3^k b ≡ 1 (mod 4)`, then
  `T^{k+2} n = T^{k+1} ((n-1)/2)`; `merge_value` gives the common value `(3^k b - 1)/4`, and
  `merge_cond_iff` says the condition means `T^{k+1} n` is even.
* `cycle_localmin_ge`: parametric in a verified orbit-minimum bound `X0`, such a point on a
  `T`-cycle satisfies `x ≥ 2 X0 + 1`; `cycle_localmin_ge_24` instantiates `X0 = 2^24`.
* `least_counterexample_shape`, `least_counterexample_mod64`: a least positive integer not
  reaching `1` under `T` is `≡ 3 (mod 4)`, has exactly one even step after its first odd run,
  and lies in `{7,11,27,31,39,43,47,59,63} mod 64`.
-/

namespace CollatzSearch
open CollatzProof

private theorem T_even' {x : ℕ} (h : x % 2 = 0) : T x = x / 2 := by
  unfold T; simp [h]
private theorem T_odd' {x : ℕ} (h : x % 2 = 1) : T x = (3 * x + 1) / 2 := by
  unfold T; simp [show x % 2 ≠ 0 by omega]

/-- Core computation of Hercher's merge lemma: with `n + 1 = 2^(k'+1) b`, `b` odd, and
`3^(k'+1) b = 4c + 1`, both `T^[k'+3] n` and `T^[k'+2] ((n-1)/2)` equal `c`. -/
private theorem merge_core {n k' b c : ℕ} (hb : b % 2 = 1) (hn : n + 1 = 2^(k'+1) * b)
    (hc : 3^(k'+1) * b = 4 * c + 1) :
    T^[k'+1+2] n = c ∧ T^[k'+1+1] ((n-1)/2) = c := by
  have h1 := odd_run_iter hn (k'+1) 0 (by omega)
  simp only [pow_zero, mul_one] at h1
  have e3 : 3^(k'+1) * b = 3 * (3^k' * b) := by rw [pow_succ]; ring
  have e2 : 2^(k'+1) * b = 2 * (2^k' * b) := by rw [pow_succ]; ring
  have hpos : 0 < 2^k' * b := Nat.mul_pos (by positivity) (by omega)
  set A := 2^k' * b with hA
  set B := 3^k' * b with hB
  rw [e3] at hc h1
  rw [e2] at hn
  constructor
  · rw [show k'+1+2 = (k'+1+1)+1 by omega, Function.iterate_succ_apply',
      Function.iterate_succ_apply']
    have hA4 : T^[k'+1] n = 4 * c := by omega
    have s1 : T (4 * c) = 2 * c := by rw [T_even' (by omega)]; omega
    have s2 : T (2 * c) = c := by rw [T_even' (by omega)]; omega
    rw [hA4, s1, s2]
  · have hnn : (n-1)/2 = A - 1 := by omega
    rw [hnn]
    have hn'1 : (A - 1) + 1 = 2^k' * b := by omega
    have h2 := odd_run_iter hn'1 k' 0 (by omega)
    simp only [pow_zero, mul_one] at h2
    rw [← hB] at h2
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    have hB4 : T^[k'] (A - 1) = 4 * (B / 4) + 2 := by omega
    have s1 : T (4 * (B / 4) + 2) = 2 * (B / 4) + 1 := by rw [T_even' (by omega)]; omega
    have s2 : T (2 * (B / 4) + 1) = c := by rw [T_odd' (by omega)]; omega
    rw [hB4, s1, s2]

/-- **Merge lemma (Hercher 2023, Lemma 9, for `T`).** If `n + 1 = 2^k b` with `k ≥ 1`, `b` odd
(so `n` is odd and followed by exactly `k` odd `T`-steps) and `3^k b ≡ 1 (mod 4)` (so at least
two even steps follow the run), then `T^{k+2} n = T^{k+1} ((n-1)/2)`. -/
theorem merge_step {n k b : ℕ} (hk : 1 ≤ k) (hb : b % 2 = 1) (hn : n + 1 = 2^k * b)
    (h4 : (3^k * b) % 4 = 1) : T^[k+2] n = T^[k+1] ((n-1)/2) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
  obtain ⟨h1, h2⟩ := merge_core (c := (3^(k'+1)*b)/4) hb hn (by omega)
  rw [h1, h2]

/-- Value of the merge point: under the hypotheses of `merge_step`,
`T^{k+2} n = (3^k b - 1)/4`. -/
theorem merge_value {n k b : ℕ} (hk : 1 ≤ k) (hb : b % 2 = 1) (hn : n + 1 = 2^k * b)
    (h4 : (3^k * b) % 4 = 1) : T^[k+2] n = (3^k * b - 1) / 4 := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
  obtain ⟨h1, _⟩ := merge_core (c := (3^(k'+1)*b)/4) hb hn (by omega)
  rw [h1]; omega

/-- The merge condition `3^k b ≡ 1 (mod 4)` holds iff `T^{k+1} n` is even, i.e. iff the odd run
of length `k` starting at `n` is followed by at least two even steps. -/
theorem merge_cond_iff {n k b : ℕ} (_hk : 1 ≤ k) (hb : b % 2 = 1) (hn : n + 1 = 2^k * b) :
    (3^k * b) % 4 = 1 ↔ (T^[k+1] n) % 2 = 0 := by
  have h1 := odd_run_iter hn k 0 (by omega)
  simp only [pow_zero, mul_one] at h1
  have hodd : (3^k * b) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod]; simp [hb]
  rw [Function.iterate_succ_apply', T_even' (by omega)]
  omega

example : T^[4] 19 = T^[3] 9 := by decide
example : T^[3] 5 = T^[2] 2 := by decide

/-! ## Orbit minima and the cycle consequence -/

/-- Every `T`-orbit has a minimum: there is an index `j0` with `T^{j0} z ≤ T^j z` for all `j`. -/
theorem exists_orbit_min (z : ℕ) : ∃ j0, ∀ j, T^[j0] z ≤ T^[j] z := by
  classical
  have hex : ∃ v, ∃ j, T^[j] z = v := ⟨z, 0, rfl⟩
  obtain ⟨j0, hj0⟩ := Nat.find_spec hex
  refine ⟨j0, fun j => ?_⟩
  rw [hj0]; exact Nat.find_min' hex ⟨j, rfl⟩

/-- If `z` reaches `1`, so does every iterate `T^i z`. -/
theorem reaches_one_iterate {z j : ℕ} (h : T^[j] z = 1) (i : ℕ) :
    ∃ j', T^[j'] (T^[i] z) = 1 := by
  by_cases hij : i ≤ j
  · refine ⟨j - i, ?_⟩
    rw [← Function.iterate_add_apply, Nat.sub_add_cancel hij, h]
  · have : T^[i] z = T^[i - j] 1 := by
      rw [← h, ← Function.iterate_add_apply, Nat.sub_add_cancel (by omega)]
    rcases T_iterate_one (i - j) with h1 | h2
    · exact ⟨0, by rw [this, h1]; rfl⟩
    · exact ⟨1, by rw [this, h2]; decide⟩

private theorem T_pos' {x : ℕ} (h : 0 < x) : 0 < T x := by
  unfold T; split <;> omega

private theorem T_iter_pos {x : ℕ} (h : 0 < x) (j : ℕ) : 0 < T^[j] x := by
  induction j with
  | zero => exact h
  | succ j ih => rw [Function.iterate_succ_apply']; exact T_pos' ih

private theorem iterate_cycle_mul {x L : ℕ} (hc : T^[L] x = x) (q : ℕ) : T^[L * q] x = x := by
  induction q with
  | zero => rfl
  | succ q ih => rw [Nat.mul_succ, Function.iterate_add_apply, hc, ih]

/-- **Merge bound for cycle points (Hercher 2023, via Lemma 9).** Let `X0` be a lower bound for
every `m > 1` that is minimal on its own `T`-orbit. If `x` lies on a `T`-cycle and
`x + 1 = 2^k b` with `k ≥ 1`, `b` odd and `3^k b ≡ 1 (mod 4)` (an odd run of exactly `k` steps
followed by at least two even steps), then `2 X0 + 1 ≤ x`. -/
theorem cycle_localmin_ge {X0 x L k b : ℕ}
    (HX : ∀ m, 1 < m → (∀ j, m ≤ T^[j] m) → X0 ≤ m)
    (hL : 0 < L) (hc : T^[L] x = x) (hk : 1 ≤ k) (hb : b % 2 = 1)
    (hn : x + 1 = 2^k * b) (h4 : (3^k * b) % 4 = 1) : 2 * X0 + 1 ≤ x := by
  have hmerge := merge_step hk hb hn h4
  obtain ⟨k', rfl⟩ : ∃ k', k = k'+1 := ⟨k-1, by omega⟩
  have e3 : 3^(k'+1) * b = 3 * (3^k' * b) := by rw [pow_succ]; ring
  have e2 : 2^(k'+1) * b = 2 * (2^k' * b) := by rw [pow_succ]; ring
  rw [e2] at hn; rw [e3] at h4
  set n' := (x - 1) / 2 with hn'
  have hx : x = 2 * n' + 1 := by omega
  -- n' ≥ 1
  have hn'pos : 1 ≤ n' := by
    rcases Nat.eq_zero_or_pos k' with h0 | h0
    · subst h0; simp at hn h4; omega
    · have : 2 ≤ 2^k' := by
        calc 2 = 2^1 := by norm_num
          _ ≤ 2^k' := Nat.pow_le_pow_right (by norm_num) h0
      have : 2 ≤ 2^k' * b := le_trans this (Nat.le_mul_of_pos_right _ (by omega))
      omega
  obtain ⟨j0, hj0⟩ := exists_orbit_min n'
  set y := T^[j0] n' with hy
  have hymin : ∀ j, y ≤ T^[j] y := by
    intro j; rw [hy, ← Function.iterate_add_apply]; exact hj0 _
  have hyle : y ≤ n' := hj0 0
  have hypos : 0 < y := T_iter_pos (by omega) j0
  have hy1 : y ≠ 1 := by
    intro hy1
    set s := L * (k' + 1 + 2 + j0) - (k' + 1 + 2) with hs
    have hLm : k' + 1 + 2 + j0 ≤ L * (k' + 1 + 2 + j0) := Nat.le_mul_of_pos_left _ hL
    have hsj : j0 ≤ k' + 1 + 1 + s := by omega
    have key : T^[k' + 1 + 1 + s] n' = x := by
      have : T^[s + (k'+1+1)] n' = T^[s] (T^[k'+1+1] n') := Function.iterate_add_apply _ _ _ _
      rw [Nat.add_comm, this, ← hmerge, ← Function.iterate_add_apply,
        show s + (k'+1+2) = L * (k' + 1 + 2 + j0) by omega, iterate_cycle_mul hc]
    have : T^[k' + 1 + 1 + s] n' = T^[k'+1+1+s - j0] 1 := by
      have hj1 : T^[j0] n' = 1 := by rw [← hy]; exact hy1
      have gen : ∀ N, j0 ≤ N → T^[N] n' = T^[N - j0] (T^[j0] n') := fun N hN => by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel hN]
      rw [gen _ hsj, hj1]
    rcases T_iterate_one (k'+1+1+s - j0) with h1 | h2
    · rw [← this, key] at h1; omega
    · rw [← this, key] at h2; omega
  have := HX y (by omega) hymin
  omega

/-- Instance at the verified range `2^24` (`min_orbit_ge_24`): a cycle point `x` followed by an
odd run of length `k ≥ 1` and then at least two even steps satisfies `x ≥ 2^25 + 1`. -/
theorem cycle_localmin_ge_24 {x L k b : ℕ} (hL : 0 < L) (hc : T^[L] x = x) (hk : 1 ≤ k)
    (hb : b % 2 = 1) (hn : x + 1 = 2^k * b) (h4 : (3^k * b) % 4 = 1) : 2^25 + 1 ≤ x := by
  have := cycle_localmin_ge (X0 := 2^24) (fun m h1 h2 => min_orbit_ge_24 h1 h2) hL hc hk hb hn h4
  norm_num at *; omega

/-! ## Least counterexample shape (Hercher 2023, Remark 10) -/

/-- `n` reaches `1` under the accelerated map `T`. -/
def ReachesOne (n : ℕ) : Prop := ∃ j, T^[j] n = 1

private theorem reaches_of_iterate {n i : ℕ} (h : ReachesOne (T^[i] n)) : ReachesOne n := by
  obtain ⟨j, hj⟩ := h
  exact ⟨j + i, by rw [Function.iterate_add_apply, hj]⟩

/-- **Least counterexample shape (Hercher 2023, Remark 10, for `T`).** If `n > 0` does not reach
`1` under `T` but every `0 < m < n` does (this covers both a least element of a nontrivial cycle
and a least divergent starting value), then `n ≡ 3 (mod 4)`, and for every factorisation
`n + 1 = 2^k b` with `b` odd we have `3^k b ≡ 3 (mod 4)`: exactly one even step follows the
first odd run. -/
theorem least_counterexample_shape {n : ℕ} (hn0 : 0 < n) (hnot : ¬ ReachesOne n)
    (hless : ∀ m, 0 < m → m < n → ReachesOne m) :
    n % 4 = 3 ∧ ∀ k b, b % 2 = 1 → n + 1 = 2^k * b → (3^k * b) % 4 = 3 := by
  have hn1 : n ≠ 1 := fun h => hnot ⟨0, by simp [h]⟩
  have hmod : n % 4 = 3 := by
    by_contra hne
    rcases (by omega : n % 2 = 0 ∨ n % 4 = 1) with he | h1
    · apply hnot
      apply reaches_of_iterate (i := 1)
      have : T^[1] n = n / 2 := by simp [T_even' he]
      rw [this]; exact hless _ (by omega) (by omega)
    · apply hnot
      apply reaches_of_iterate (i := 2)
      obtain ⟨q, rfl⟩ : ∃ q, n = 4 * q + 1 := ⟨n / 4, by omega⟩
      have s1 : T (4 * q + 1) = 6 * q + 2 := by rw [T_odd' (by omega)]; omega
      have s2 : T (6 * q + 2) = 3 * q + 1 := by rw [T_even' (by omega)]; omega
      have : T^[2] (4 * q + 1) = 3 * q + 1 := by
        rw [Function.iterate_succ_apply', Function.iterate_one, s1, s2]
      rw [this]; exact hless _ (by omega) (by omega)
  refine ⟨hmod, fun k b hb hnk => ?_⟩
  have hk : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h0 | h0
    · subst h0; simp at hnk; omega
    · exact h0
  have hodd : (3^k * b) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod]; simp [hb]
  by_contra h3
  have h4 : (3^k * b) % 4 = 1 := by omega
  have hm := merge_step hk hb hnk h4
  apply hnot
  obtain ⟨j, hj⟩ := hless ((n-1)/2) (by omega) (by omega)
  obtain ⟨j', hj'⟩ := reaches_one_iterate hj (k+1)
  apply reaches_of_iterate (i := k+2)
  exact ⟨j', by rw [hm, hj']⟩

/-- Corollary of `least_counterexample_shape`: a least counterexample satisfies
`n mod 64 ∈ {7, 11, 27, 31, 39, 43, 47, 59, 63}`. -/
theorem least_counterexample_mod64 {n : ℕ} (hn0 : 0 < n) (hnot : ¬ ReachesOne n)
    (hless : ∀ m, 0 < m → m < n → ReachesOne m) :
    n % 64 = 7 ∨ n % 64 = 11 ∨ n % 64 = 27 ∨ n % 64 = 31 ∨ n % 64 = 39 ∨ n % 64 = 43 ∨
      n % 64 = 47 ∨ n % 64 = 59 ∨ n % 64 = 63 := by
  obtain ⟨h4, hc⟩ := least_counterexample_shape hn0 hnot hless
  have c2 := hc 2 ((n+1)/4)
  have c3 := hc 3 ((n+1)/8)
  have c4 := hc 4 ((n+1)/16)
  norm_num at c2 c3 c4
  omega

end CollatzSearch

#print axioms CollatzSearch.merge_step
#print axioms CollatzSearch.merge_value
#print axioms CollatzSearch.merge_cond_iff
#print axioms CollatzSearch.cycle_localmin_ge
#print axioms CollatzSearch.cycle_localmin_ge_24
#print axioms CollatzSearch.least_counterexample_shape
#print axioms CollatzSearch.least_counterexample_mod64
