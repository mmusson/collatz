import CollatzSearch.CycleMin
import Mathlib.Tactic

/-!
# Gas-station (good) rotation on a `T`-cycle

**UNCONDITIONAL.  Classical in spirit** (the gas-station / cycle-lemma rotation that drives
the round-41 two-rotation argument, stated per step so no run decomposition is needed).
**NOT progress on `no_nontrivial_cycles`**, which remains OPEN.

* `sigma_affine` (shifted Terras identity): `2^j (T^j n + 1) = 3^{S_j(n)} (n+1) + σ_j(n)`,
  where `σ` collects a `3^{S}` term at every *even* step.
* `sigma_le_of_good`: if every suffix of the length-`j` orbit window from `n` satisfies
  `3^{S} ≤ 2^{length}` (`Good j n`), then `2σ_j(n) ≤ (j − S_j(n))·2^j`.
* `exists_good_rotation`: every positive `T`-cycle has a rotation point `y = T^s x`, `s < L`,
  with `Good L y` (minimise `3^{S_i}/2^i` over one period window `[L, 2L)`).
* `good_rotation_bound`: at that point `(y+1)(2^L − 3^k)·2 ≤ (L − k)·2^L`.
* `good_rotation_run_bound`: if `y` begins a run of `j` odd steps, `2^j (2^L − 3^k)·2 ≤ (L−k)2^L`.
* `min_bound_of_good_rotation`: the cycle minimum satisfies `(m+1)(2^L − 3^k)·2 ≤ (L−k)2^L`,
  i.e. `m < L·2^{L−1}/(2^L − 3^k)` (Crandall/Eliahou-type bound).

## Scoping (`GoodRotation`, numerics, NOT a theorem)
Size arguments alone (`u_i ≥ 2^{k_i}` for run starts `u_i = x_i + 1`, plus a relative gap
`1 − 3^k/2^L = 2^{−δk}`) exclude `m`-circuits for large `k` iff
`δ < δ*_m = (θ−1)/(θ^m−1)`, `θ = log₂ 3`: `δ*_2 ≈ 0.387`, `δ*_3 ≈ 0.196`, `δ*_4 ≈ 0.110`
(proved for `m = 2` by `TwoCircEllison`; for `m = 3, 4` supported by random search with local refinement
and matching extremal constructions).  Ellison 1971 gives `δ ≈ 0.229` in these units, so
size + Ellison covers `m ≤ 2` (`TwoCircEllison`) but NOT `m = 3`.  Extremal `m = 3` profile:
`κ = (0.311, 0.493, 0.196)`, `λ = (0, 0.585, 0)`.
-/

namespace CollatzSearch
open CollatzProof

/-- Shifted Terras remainder: `σ_0 = 0`, `σ_{j+1}(n) = 2σ_j(Tn) + [n even]·3^{S_j(Tn)}`. -/
def sigma : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j+1, n => 2 * sigma j (T n) + (if n % 2 = 0 then 3 ^ oddSteps j (T n) else 0)

example : sigma 2 1 = 2 := by decide

/-- For odd `n`, `2(Tn+1) = 3(n+1)`. -/
theorem two_mul_T_add_one_odd {n : ℕ} (h : n % 2 = 1) : 2 * (T n + 1) = 3 * (n + 1) := by
  rw [T_of_odd h]; omega

/-- For even `n`, `2(Tn+1) = (n+1)+1`. -/
theorem two_mul_T_add_one_even {n : ℕ} (h : n % 2 = 0) : 2 * (T n + 1) = n + 1 + 1 := by
  rw [T_of_even h]; omega

/-- **Shifted Terras identity** (unconditional): `2^j (T^j n + 1) = 3^{S_j(n)}(n+1) + σ_j(n)`. -/
theorem sigma_affine (j n : ℕ) :
    2 ^ j * (T^[j] n + 1) = 3 ^ oddSteps j n * (n + 1) + sigma j n := by
  induction j generalizing n with
  | zero => simp [oddSteps, sigma]
  | succ j ih =>
    rw [Function.iterate_succ_apply, pow_succ, mul_comm (2 ^ j) 2, mul_assoc, ih (T n)]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have e := two_mul_T_add_one_even h
      simp only [oddSteps, sigma, h, ite_true, add_zero]
      calc 2 * (3 ^ oddSteps j (T n) * (T n + 1) + sigma j (T n))
          = 3 ^ oddSteps j (T n) * (2 * (T n + 1)) + 2 * sigma j (T n) := by ring
        _ = _ := by rw [e]; ring
    · have e := two_mul_T_add_one_odd h
      simp only [oddSteps, sigma, h, one_ne_zero, ite_false, add_zero]
      calc 2 * (3 ^ oddSteps j (T n) * (T n + 1) + sigma j (T n))
          = 3 ^ oddSteps j (T n) * (2 * (T n + 1)) + 2 * sigma j (T n) := by ring
        _ = _ := by rw [e, pow_succ]; ring

/-- `Good j n`: every suffix window of the length-`j` orbit from `n` has `3^{#odd} ≤ 2^{length}`. -/
def Good (j n : ℕ) : Prop := ∀ t, t ≤ j → 3 ^ oddSteps (j - t) (T^[t] n) ≤ 2 ^ (j - t)

/-- If `Good j n` then `2σ_j(n) ≤ (j − S_j(n))·2^j` (unconditional). -/
theorem sigma_le_of_good {j n : ℕ} (h : Good j n) : 2 * sigma j n ≤ (j - oddSteps j n) * 2 ^ j := by
  induction j generalizing n with
  | zero => simp [sigma]
  | succ j ih =>
    have hg : Good j (T n) := by
      intro t ht
      have := h (t + 1) (by omega)
      rw [show j + 1 - (t + 1) = j - t by omega, Function.iterate_succ_apply] at this
      exact this
    have h1 : 3 ^ oddSteps j (T n) ≤ 2 ^ j := by
      have := h 1 (by omega)
      simpa using this
    have ihn := ih hg
    have hS := oddSteps_le j (T n)
    obtain ⟨a, ha⟩ : ∃ a, j = oddSteps j (T n) + a := ⟨j - oddSteps j (T n), by omega⟩
    rw [show j - oddSteps j (T n) = a by omega] at ihn
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · simp only [sigma, oddSteps, hn, ite_true, add_zero]
      rw [show j + 1 - oddSteps j (T n) = a + 1 by omega, pow_succ]
      nlinarith
    · simp only [sigma, oddSteps, hn, one_ne_zero, ite_false, add_zero]
      rw [show j + 1 - (oddSteps j (T n) + 1) = a by omega, pow_succ]
      nlinarith

/-- Alias of `oddSteps_cycle_invariant`: `S_L(T^i x) = S_L(x)` on a cycle. -/
theorem oddSteps_rotate {x L : ℕ} (h : T^[L] x = x) (i : ℕ) :
    oddSteps L (T^[i] x) = oddSteps L x := oddSteps_cycle_invariant h i

/-- `S_{u+L} = S_u + k` on a cycle. -/
theorem oddSteps_add_period {x L : ℕ} (h : T^[L] x = x) (u : ℕ) :
    oddSteps (u + L) x = oddSteps u x + oddSteps L x := by
  rw [oddSteps_add, oddSteps_rotate h]

/-- **Gas-station lemma** (UNCONDITIONAL, classical in spirit, not Goal progress): every positive
`T`-cycle `T^L x = x` has a rotation point `T^s x`, `s < L`, with `Good L (T^s x)`. -/
theorem exists_good_rotation {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (h : T^[L] x = x) :
    ∃ s, s < L ∧ Good L (T^[s] x) := by
  let F : ℕ → ℚ := fun i => (3 : ℚ) ^ oddSteps i x / 2 ^ i
  have hne : (Finset.Ico L (2 * L)).Nonempty := ⟨L, by simp; omega⟩
  obtain ⟨p, hp, hmin⟩ := Finset.exists_min_image _ F hne
  simp only [Finset.mem_Ico] at hp
  have hk : (3 : ℚ) ^ oddSteps L x ≤ 2 ^ L := by
    exact_mod_cast (three_pow_lt_two_pow_of_cycle hx hL h).le
  have hper : ∀ u, F (u + L) ≤ F u := by
    intro u
    simp only [F]
    rw [oddSteps_add_period h, pow_add, pow_add, div_le_div_iff₀ (by positivity) (by positivity)]
    have : (0:ℚ) ≤ 3 ^ oddSteps u x * 2 ^ u := by positivity
    nlinarith
  have key : ∀ u, p - L ≤ u → u ≤ p → F p ≤ F u := by
    intro u h1 h2
    by_cases hu : L ≤ u
    · exact hmin u (by simp; omega)
    · exact le_trans (hmin (u + L) (by simp; omega)) (hper u)
  refine ⟨p - L, by omega, ?_⟩
  intro t ht
  set u := p - L + t with hu
  have hpu : p = u + (L - t) := by omega
  have hFu := key u (by omega) (by omega)
  simp only [F] at hFu
  rw [hpu, oddSteps_add, pow_add, pow_add, div_le_div_iff₀ (by positivity) (by positivity)] at hFu
  have hT : T^[u] x = T^[t] (T^[p - L] x) := by
    rw [hu, add_comm, Function.iterate_add_apply]
  rw [← hT]
  have hpos : (0:ℚ) < 3 ^ oddSteps u x * 2 ^ u := by positivity
  have : (3:ℚ) ^ oddSteps (L - t) (T^[u] x) ≤ 2 ^ (L - t) := by
    by_contra hc
    push Not at hc
    have := mul_lt_mul_of_pos_left hc hpos
    nlinarith
  exact_mod_cast this

/-- (UNCONDITIONAL, not Goal progress) On a positive `T`-cycle with `k` odd steps in `L`, there is a
good rotation point `y = T^s x` with `(y+1)(2^L − 3^k)·2 ≤ (L − k)·2^L`. -/
theorem good_rotation_bound {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (h : T^[L] x = x) :
    ∃ s, s < L ∧ Good L (T^[s] x) ∧
      (T^[s] x + 1) * (2 ^ L - 3 ^ oddSteps L x) * 2 ≤ (L - oddSteps L x) * 2 ^ L := by
  obtain ⟨s, hs, hg⟩ := exists_good_rotation hx hL h
  refine ⟨s, hs, hg, ?_⟩
  have hk := three_pow_lt_two_pow_of_cycle hx hL h
  have hA := sigma_affine L (T^[s] x)
  rw [iterate_cycle h s, oddSteps_rotate h s] at hA
  have hB := sigma_le_of_good hg
  rw [oddSteps_rotate h s] at hB
  have hC : (T^[s] x + 1) * (2 ^ L - 3 ^ oddSteps L x) = sigma L (T^[s] x) := by
    rw [Nat.mul_sub, mul_comm (T^[s] x + 1) (2 ^ L), hA, mul_comm (T^[s] x + 1)]
    omega
  rw [hC]; omega

/-- If `y, Ty, …, T^{j−1}y` are all odd then `2^j ∣ y + 1`. -/
theorem run_start_pow_dvd {y j : ℕ} (h : ∀ i, i < j → T^[i] y % 2 = 1) : 2 ^ j ∣ y + 1 := by
  induction j generalizing y with
  | zero => simp
  | succ j ih =>
    have hy : y % 2 = 1 := by simpa using h 0 (by omega)
    have hT : 2 ^ j ∣ T y + 1 := ih (fun i hi => by
      have := h (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    have h3 : 2 ^ (j + 1) ∣ 3 * (y + 1) := by
      rw [← two_mul_T_add_one_odd hy, pow_succ, mul_comm]
      exact Nat.mul_dvd_mul_left 2 hT
    have hc : Nat.Coprime (2 ^ (j + 1)) 3 := Nat.Coprime.pow_left _ (by norm_num)
    exact hc.dvd_of_dvd_mul_left h3

/-- (UNCONDITIONAL, not Goal progress) On a positive `T`-cycle there is `s < L` such that whenever
`T^s x` starts `j` consecutive odd steps, `2^j (2^L − 3^k)·2 ≤ (L − k)·2^L`. -/
theorem good_rotation_run_bound {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (h : T^[L] x = x) :
    ∃ s, s < L ∧ ∀ j, (∀ i, i < j → T^[i] (T^[s] x) % 2 = 1) →
      2 ^ j * (2 ^ L - 3 ^ oddSteps L x) * 2 ≤ (L - oddSteps L x) * 2 ^ L := by
  obtain ⟨s, hs, -, hb⟩ := good_rotation_bound hx hL h
  refine ⟨s, hs, fun j hj => le_trans ?_ hb⟩
  have := Nat.le_of_dvd (by omega) (run_start_pow_dvd hj)
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ this)

/-- (UNCONDITIONAL, not Goal progress) The minimum `m` of a positive `T`-cycle satisfies
`(m+1)(2^L − 3^k)·2 ≤ (L − k)·2^L`. -/
theorem min_bound_of_good_rotation {m L : ℕ} (hm : 0 < m) (hL : 0 < L) (h : T^[L] m = m)
    (hmin : ∀ i, m ≤ T^[i] m) :
    (m + 1) * (2 ^ L - 3 ^ oddSteps L m) * 2 ≤ (L - oddSteps L m) * 2 ^ L := by
  obtain ⟨s, -, -, hb⟩ := good_rotation_bound hm hL h
  refine le_trans ?_ hb
  exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (by have := hmin s; omega))

end CollatzSearch

#print axioms CollatzSearch.sigma_affine
#print axioms CollatzSearch.sigma_le_of_good
#print axioms CollatzSearch.oddSteps_rotate
#print axioms CollatzSearch.oddSteps_add_period
#print axioms CollatzSearch.exists_good_rotation
#print axioms CollatzSearch.good_rotation_bound
#print axioms CollatzSearch.run_start_pow_dvd
#print axioms CollatzSearch.good_rotation_run_bound
#print axioms CollatzSearch.min_bound_of_good_rotation
