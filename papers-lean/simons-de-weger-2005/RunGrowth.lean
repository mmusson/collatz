import RunsBridge
import Collatz.Diophantine
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic

/-!
# Run growth and the minimum bound (Simons–de Weger m-cycle machinery, pure ℕ)

**CLASSICAL.** This is the engine of the Simons–de Weger (2005) upper bound for the number of
odd steps of an `m`-cycle (cf. Hercher 2023, arXiv:2201.00406, Lemma 14 and the bound
`K < 1.4784·m·δ^m`), in an exact pure-`ℕ` form with the exponent `8/5 ≥ log₂ 3` in place of
`δ = log₂ 3`.

* `W r = ∑_{j<r} 8^j 5^{r-1-j}` (`W 0 = 0`, `W (r+1) = 5^r + 8 W r`).
* `odd_run_iter`, `even_run_iter`: explicit form of `T` along an odd / even stretch.
* `runs_growth`: if `x` is odd, `T^N x` odd, `T^{N-1} x` even (the window ends just after an
  even→odd transition) and `(x+1)^{5^e} ≤ 2^c`, then
  `5^{e+ρ} S_N(x) ≤ 5 c W(ρ)`, `ρ = oddRuns N x`.  With `e = 0`:
  `S_N(x) ≤ log₂(x+1) · ∑_{j<ρ} (8/5)^j`.  Engine: consecutive run starts satisfy
  `(x'+1)^5 ≤ (x+1)^8`, and a run of length `k` from `x` has `2^k ∣ x+1`.
* `min_add_one_le`: Bernoulli applied to the run inequality: `2^L X^r ≤ 3^K (X+1)^r`,
  `3^K < 2^L`, `2^L ≤ 2^s (2^L − 3^K)` ⇒ `X + 1 ≤ r 2^s`.
* `pred_even_of_min`: the point before an odd cycle minimum is even.
* `runs_bound_of_min`: for the odd minimum `m` of a `T`-cycle (window `L`, `k = S_L(m)`,
  `r = oddRuns L m ≤ 2^t`) with gap exponent `s`: `5^r k ≤ 5 (s+t) W(r)`.

`oddRuns L m` counts even→odd transitions in the chosen window `L`; if `L` is `t` times the
minimal period, it is `t` times the per-lap count (`oddRuns_mul`).
-/

namespace Collatz
open CollatzProof

/-- `W 0 = 0`, `W (r+1) = 5^r + 8 W r`, so `W r = ∑_{j<r} 8^j 5^{r-1-j}`. -/
def W : ℕ → ℕ
  | 0 => 0
  | r+1 => 5^r + 8 * W r

/-- Odd stretch: if `x + 1 = 2^k a`, then for `i + j = k`, `T^j x + 1 = 3^j 2^i a`
(so `T^j x` is odd for `j < k` when `a` is odd, and `T^k x = 3^k a − 1`). -/
theorem odd_run_iter {x k a : ℕ} (hxa : x + 1 = 2^k * a) :
    ∀ j i, i + j = k → T^[j] x + 1 = 3^j * 2^i * a := by
  intro j
  induction j with
  | zero => intro i hi; simp only [Function.iterate_zero, id, pow_zero, one_mul]; rw [hxa]; congr 2; omega
  | succ j ih =>
    intro i hi
    have h := ih (i+1) (by omega)
    rw [Function.iterate_succ_apply']
    generalize T^[j] x = z at h ⊢
    have hM : 3^j * 2^(i+1) * a = 2 * (3^j * 2^i * a) := by ring
    have hM' : 3^(j+1) * 2^i * a = 3 * (3^j * 2^i * a) := by ring
    rw [hM] at h; rw [hM']
    generalize 3^j * 2^i * a = M at h ⊢
    have hz : z % 2 = 1 := by omega
    rw [T_of_odd hz]; omega

/-- Even stretch: if `z = 2^l b`, then `T^i z = 2^{l−i} b` for `i ≤ l`. -/
theorem even_run_iter {z l b : ℕ} (hz : z = 2^l * b) : ∀ i, i ≤ l → T^[i] z = 2^(l-i) * b := by
  intro i
  induction i with
  | zero => intro _; simpa using hz
  | succ i ih =>
    intro hi
    rw [Function.iterate_succ_apply', ih (by omega)]
    have e : 2^(l-i) = 2 * 2^(l-(i+1)) := by
      rw [← pow_succ']; congr 1; omega
    rw [e, T_of_even (by rw [mul_assoc]; exact Nat.mul_mod_right _ _)]
    rw [mul_assoc, Nat.mul_div_cancel_left _ (by norm_num)]

/-- If `T y` is even, `y` is not the start of an odd run. -/
theorem runStart_of_next_even {y : ℕ} (h : T y % 2 = 0) : runStart y = 0 := by
  unfold runStart; simp [h]

/-- **Run growth (classical, Simons–de Weger / Hercher Lemma 14 in pure ℕ form).**
If `x` is odd, `N ≥ 1`, `T^N x` is odd, `T^{N−1} x` is even and `(x+1)^{5^e} ≤ 2^c`, then
`5^{e+ρ}·S_N(x) ≤ 5·c·W(ρ)` with `ρ = oddRuns N x`. -/
theorem runs_growth : ∀ (N x e c : ℕ), x % 2 = 1 → 0 < N → (T^[N] x) % 2 = 1 →
    (T^[N-1] x) % 2 = 0 → (x+1)^(5^e) ≤ 2^c →
    5^(e + oddRuns N x) * oddSteps N x ≤ 5 * c * W (oddRuns N x) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N IH =>
  intro x e c hx hN hend hprev hxc
  obtain ⟨k, a, ha, hka⟩ := Nat.exists_eq_two_pow_mul_odd (n := x+1) (by omega)
  have ha1 : a % 2 = 1 := Nat.odd_iff.mp ha
  have hk1 : 1 ≤ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hka; omega
    · exact h
  have hA := odd_run_iter hka
  have hodd : ∀ j < k, T^[j] x % 2 = 1 := by
    intro j hj
    have h := hA j (k-j) (by omega)
    have : 2^(k-j) = 2 * 2^(k-j-1) := by rw [← pow_succ']; congr 1; omega
    rw [this] at h
    have : 3^j * (2 * 2^(k-j-1)) * a = 2 * (3^j * 2^(k-j-1) * a) := by ring
    omega
  have hz0 : T^[k] x + 1 = 3^k * a := by simpa using hA k 0 (by omega)
  set z0 := T^[k] x with hz0def
  have h3k : (3^k * a) % 2 = 1 := by
    rw [Nat.mul_mod, Nat.pow_mod]; simp [ha1]
  have h3k3 : 3 ≤ 3^k * a := by
    have : 3 ≤ 3^k := by
      calc 3 = 3^1 := by norm_num
        _ ≤ 3^k := Nat.pow_le_pow_right (by norm_num) hk1
    have : 1 ≤ a := by omega
    nlinarith
  have hz0e : z0 % 2 = 0 := by omega
  obtain ⟨l, b, hb, hlb⟩ := Nat.exists_eq_two_pow_mul_odd (n := z0) (by omega)
  have hb1 : b % 2 = 1 := Nat.odd_iff.mp hb
  have hl1 : 1 ≤ l := by
    rcases Nat.eq_zero_or_pos l with h | h
    · subst h; simp at hlb; omega
    · exact h
  have hB := even_run_iter hlb
  have heven : ∀ i < l, T^[i] z0 % 2 = 0 := by
    intro i hi
    rw [hB i hi.le]
    have : 2^(l-i) = 2 * 2^(l-i-1) := by rw [← pow_succ']; congr 1; omega
    rw [this, mul_assoc]; exact Nat.mul_mod_right _ _
  have hzl : T^[l] z0 = b := by simpa using hB l le_rfl
  have hxkl : T^[k+l] x = b := by
    rw [add_comm, Function.iterate_add_apply, ← hz0def, hzl]
  -- oddSteps / oddRuns of the segment
  have hS : oddSteps (k+l) x = k := by
    rw [oddSteps_add, oddSteps_odd_run k x hodd, ← hz0def, oddSteps_even_run l z0 heven]; simp
  have hR : oddRuns (k+l) x = 1 := by
    rw [oddRuns_add]
    have h1 : oddRuns k x = 0 := by
      rw [oddRuns_eq_sum]
      exact Finset.sum_eq_zero (fun i hi => runStart_of_odd (hodd i (Finset.mem_range.mp hi)))
    have h2 : oddRuns l z0 = 1 := by
      obtain ⟨l', rfl⟩ : ∃ l', l = l' + 1 := ⟨l-1, by omega⟩
      rw [oddRuns_add, oddRuns_one]
      have h3 : oddRuns l' z0 = 0 := by
        rw [oddRuns_eq_sum]
        refine Finset.sum_eq_zero (fun i hi => runStart_of_next_even ?_)
        have hi' := Finset.mem_range.mp hi
        have := heven (i+1) (by omega)
        rwa [Function.iterate_succ_apply'] at this
      rw [h3]
      have h4 : runStart (T^[l'] z0) = 1 := by
        refine runStart_of_even_odd (heven l' (by omega)) ?_
        rw [← Function.iterate_succ_apply' T l' z0, hzl]; exact hb1
      omega
    rw [h1, ← hz0def, h2]
  -- size of next start
  have h2k : 2^k ≤ x + 1 := by rw [hka]; exact Nat.le_mul_of_pos_right _ (by omega)
  have hbsz : 2^k * (b + 1) ≤ 3^k * (x + 1) := by
    have : b + 1 ≤ 3^k * a := by
      have : 2 * b ≤ z0 := by
        rw [hlb]
        have : 2 ≤ 2^l := by
          calc 2 = 2^1 := by norm_num
            _ ≤ 2^l := Nat.pow_le_pow_right (by norm_num) hl1
        nlinarith
      omega
    rw [hka]
    calc 2^k * (b+1) ≤ 2^k * (3^k * a) := Nat.mul_le_mul_left _ this
      _ = 3^k * (2^k * a) := by ring
  have hgrow : (b+1)^5 ≤ (x+1)^8 := by
    have e1 : (3^k)^5 ≤ (2^k)^8 := by
      rw [← pow_mul, ← pow_mul, mul_comm k 5, mul_comm k 8, pow_mul, pow_mul]
      exact Nat.pow_le_pow_left (by norm_num) k
    have e2 : (2^k)^5 * (b+1)^5 ≤ (2^k)^5 * ((2^k)^3 * (x+1)^5) := by
      calc (2^k)^5 * (b+1)^5 = (2^k * (b+1))^5 := by ring
        _ ≤ (3^k * (x+1))^5 := Nat.pow_le_pow_left hbsz 5
        _ = (3^k)^5 * (x+1)^5 := by ring
        _ ≤ (2^k)^8 * (x+1)^5 := Nat.mul_le_mul_right _ e1
        _ = (2^k)^5 * ((2^k)^3 * (x+1)^5) := by ring
    have e3 := Nat.le_of_mul_le_mul_left e2 (by positivity)
    calc (b+1)^5 ≤ (2^k)^3 * (x+1)^5 := e3
      _ ≤ (x+1)^3 * (x+1)^5 := Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h2k 3)
      _ = (x+1)^8 := by ring
  have hbase : 5^e * k ≤ c := by
    have : 2^(k * 5^e) ≤ 2^c := by
      calc 2^(k * 5^e) = (2^k)^(5^e) := pow_mul _ _ _
        _ ≤ (x+1)^(5^e) := Nat.pow_le_pow_left h2k _
        _ ≤ 2^c := hxc
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp this
    linarith [mul_comm k (5^e)]
  -- N ≥ k + l
  have hNkl : k + l ≤ N := by
    by_contra hlt
    push Not at hlt
    rcases Nat.lt_or_ge (N-1) k with h1 | h1
    · have := hodd (N-1) h1; omega
    · have hN' : T^[N] x = T^[N-k] z0 := by
        rw [hz0def, ← Function.iterate_add_apply]; congr 1; omega
      have := heven (N-k) (by omega)
      omega
  rcases Nat.eq_or_lt_of_le hNkl with hEq | hLt
  · subst hEq
    rw [hR, hS]
    simp only [W, pow_zero, mul_zero, add_zero, mul_one]
    rw [pow_succ]; nlinarith
  · set N' := N - (k+l) with hN'def
    have hNsplit : N = (k+l) + N' := by omega
    have hIH := IH N' (by omega) b (e+1) (8*c) hb1 (by omega)
      (by rw [← hxkl, ← Function.iterate_add_apply, add_comm, ← hNsplit]; exact hend)
      (by
        rw [← hxkl, ← Function.iterate_add_apply]
        have : N' - 1 + (k+l) = N - 1 := by omega
        rw [this]; exact hprev)
      (by
        calc (b+1)^(5^(e+1)) = ((b+1)^5)^(5^e) := by rw [pow_succ, mul_comm, pow_mul]
          _ ≤ ((x+1)^8)^(5^e) := Nat.pow_le_pow_left hgrow _
          _ = ((x+1)^(5^e))^8 := by rw [← pow_mul, ← pow_mul, mul_comm]
          _ ≤ (2^c)^8 := Nat.pow_le_pow_left hxc _
          _ = 2^(8*c) := by rw [← pow_mul, mul_comm])
    rw [hNsplit, oddRuns_add, oddSteps_add, hR, hS, hxkl]
    set ρ := oddRuns N' b
    set S' := oddSteps N' b
    have hW : W (1 + ρ) = 5^ρ + 8 * W ρ := by rw [add_comm]; rfl
    rw [hW]
    have e1 : 5^(e + (1 + ρ)) = 5 * 5^ρ * 5^e := by rw [pow_add, pow_add]; ring
    have e2 : 5^(e + 1 + ρ) = 5 * 5^ρ * 5^e := by rw [pow_add, pow_add]; ring
    rw [e2] at hIH; rw [e1]
    have h5 := Nat.mul_le_mul_left (5 * 5^ρ) hbase
    calc 5 * 5^ρ * 5^e * (k + S') = 5 * 5^ρ * (5^e * k) + 5 * 5^ρ * 5^e * S' := by ring
      _ ≤ 5 * 5^ρ * c + 5 * (8 * c) * W ρ := Nat.add_le_add h5 hIH
      _ = 5 * c * (5^ρ + 8 * W ρ) := by ring

/-- Minimum bound (Bernoulli on the run inequality): if `r ≥ 1`, `2^L X^r ≤ 3^K (X+1)^r`,
`3^K < 2^L` and `2^L ≤ 2^s (2^L − 3^K)`, then `X + 1 ≤ r·2^s`. -/
theorem min_add_one_le {X K L r s : ℕ} (hr : 1 ≤ r) (h : 2^L * X^r ≤ 3^K * (X+1)^r)
    (h3 : 3^K < 2^L) (hgap : 2^L ≤ 2^s * (2^L - 3^K)) : X + 1 ≤ r * 2^s := by
  rcases Nat.lt_or_ge (X+1) r with hlt | hge
  · exact le_trans hlt.le (Nat.le_mul_of_pos_right _ (by positivity))
  · have hB := bernoulli_nat (X+1) r hge
    rw [show X + 1 - 1 = X by omega] at hB
    obtain ⟨D, hD⟩ : ∃ D, 2^L = D + 3^K := ⟨2^L - 3^K, by omega⟩
    have hD0 : 0 < D := by omega
    rw [hD, show D + 3^K - 3^K = D by omega] at hgap
    obtain ⟨u, hu⟩ : ∃ u, X + 1 = u + r := ⟨X + 1 - r, by omega⟩
    rw [hu, show u + r - r = u by omega] at hB
    rw [hu]
    set Y := u + r with hY
    set E := 3^K
    have hP : 0 < Y^r := by positivity
    have c1 : Y^r * ((D + E) * u) ≤ Y^r * (E * Y) := by
      calc Y^r * ((D + E) * u) = (D + E) * (Y^r * u) := by ring
        _ ≤ (D + E) * (Y * X^r) := Nat.mul_le_mul_left _ hB
        _ = Y * ((D + E) * X^r) := by ring
        _ ≤ Y * (E * Y^r) := by rw [← hD]; exact Nat.mul_le_mul_left _ (by rw [← hu]; exact h)
        _ = Y^r * (E * Y) := by ring
    have c2 := Nat.le_of_mul_le_mul_left c1 hP
    have c3 : D * u ≤ E * r := by rw [hY] at c2; nlinarith
    have c4 : D * Y ≤ D * (r * 2^s) := by
      calc D * Y = D * u + D * r := by rw [hY]; ring
        _ ≤ E * r + D * r := Nat.add_le_add_right c3 _
        _ = (D + E) * r := by ring
        _ ≤ 2^s * D * r := Nat.mul_le_mul_right _ hgap
        _ = D * (r * 2^s) := by ring
    exact Nat.le_of_mul_le_mul_left c4 hD0

/-- The predecessor on the cycle of an odd cycle minimum is even:
`x` odd, `T^L x = x` (`L > 0`), `x ≤ T^j x ∀ j` ⇒ `T^{L−1} x` even. -/
theorem pred_even_of_min {x L : ℕ} (hodd : x % 2 = 1) (hL : 0 < L) (hc : T^[L] x = x)
    (hmin : ∀ j, x ≤ T^[j] x) : (T^[L-1] x) % 2 = 0 := by
  have hT : T (T^[L-1] x) = x := by
    rw [← Function.iterate_succ_apply' T (L-1) x, show (L-1).succ = L by omega, hc]
  have hm := hmin (L-1)
  generalize T^[L-1] x = z at hT hm ⊢
  by_contra hz
  have hz1 : z % 2 = 1 := by omega
  rw [T_of_odd hz1] at hT
  omega

/-- **Simons–de Weger upper bound (pure ℕ form, classical).** For the odd minimum `m` of a
`T`-cycle of length `L > 0` with `k = S_L(m)`, `3^k < 2^L`, gap `2^L ≤ 2^s (2^L − 3^k)` and
`r = oddRuns L m ≤ 2^t`: `5^r k ≤ 5 (s+t) W(r)`, i.e. `k ≤ (s+t) ∑_{j<r} (8/5)^j`. -/
theorem runs_bound_of_min {m L s t : ℕ} (hodd : m % 2 = 1) (hL : 0 < L) (hc : T^[L] m = m)
    (hmin : ∀ j, m ≤ T^[j] m) (h3 : 3^(oddSteps L m) < 2^L)
    (hgap : 2^L ≤ 2^s * (2^L - 3^(oddSteps L m))) (ht : oddRuns L m ≤ 2^t) :
    5^(oddRuns L m) * oddSteps L m ≤ 5 * (s + t) * W (oddRuns L m) := by
  have hm0 : 0 < m := by omega
  have hr := oddRuns_pos_of_cycle hm0 hL hc
  have hineq := cycle_run_ineq hm0 hc hmin
  have hA := min_add_one_le hr hineq h3 hgap
  have hB : m + 1 ≤ 2^(s+t) := by
    calc m + 1 ≤ oddRuns L m * 2^s := hA
      _ ≤ 2^t * 2^s := Nat.mul_le_mul_right _ ht
      _ = 2^(s+t) := by rw [pow_add, mul_comm]
  have := runs_growth L m 0 (s+t) hodd hL (by rw [hc]; exact hodd)
    (pred_even_of_min hodd hL hc hmin) (by simpa using hB)
  simpa using this

end Collatz

#print axioms Collatz.odd_run_iter
#print axioms Collatz.even_run_iter
#print axioms Collatz.runs_growth
#print axioms Collatz.min_add_one_le
#print axioms Collatz.pred_even_of_min
#print axioms Collatz.runs_bound_of_min
