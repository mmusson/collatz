import CollatzSearch.Transfer
import CollatzSearch.RunsBridge
import Mathlib.Data.Nat.Log

/-!
# `SchemeHyp ⇒ LinFormHyp` (wall (b) interface), part 2

* `SchemeHyp a b c0` (**UNPROVED, CONDITIONAL input**, never an axiom): `a < b`, and for every
  `n` there are three integer triples `u, v, w` with `det3 u v w ≠ 0` such that every
  `x ∈ {u,v,w}` has `|x₁ + x₂ log 2 + x₃ log 3| ≤ 2^{c0}/2^{bn}` and `|x₂|, |x₃| ≤ 2^{c0+an}`.
  This is the output shape of Rhin-type Hermite–Padé constructions (coefficients `e^{αm}`,
  forms `e^{−βm}`, `α < β`, three consecutive forms independent) after reparametrizing
  `m ≈ bn·log 2/β` with `a/b ≥ α/β`; rounding and the use of three consecutive levels are
  absorbed into `c0`.  The proof picks `n = ⌈log₂(2^{2c0+3}·2k)⌉`, which is sharp when
  `b = a + 1`; any scheme with rates `α < β` can be reparametrized to `b = a+1` with
  `a = ⌈α/(β−α)⌉`, giving `μ = 2a`.  Whether any explicit literature scheme satisfies it is **unverified**
  here (see `Scratch/scheme_scoping.py` and.
* `linFormHyp_of_scheme` (**unconditional implication**):
  `SchemeHyp a b c0 ⇒ LinFormHyp 1 (3 + 2c0 + 2a(2c0+5)) (2a)`.
* `few_runs_cycle_trivial_of_scheme`, `nontrivial_C_cycle_three_runs_of_scheme`:
  **CONDITIONAL on `SchemeHyp`** (plus the numeric side condition
  `8(c + 17μ + 2) ≤ 2^16`): no nontrivial `T`-cycle with `≤ 2` odd runs, for every `k`.

Round-10 critic remarks (paper remarks, not formalized):
1. Geometry of numbers: by Minkowski, three independent integer forms in `1, log 2, log 3` with
   coefficients `≤ 2^{an}` cannot all be smaller than about `2^{-2an}`, so `SchemeHyp` forces
   `b ≲ 2a` asymptotically; in particular `a ≥ 1`.  Whether any explicit scheme satisfies
   `SchemeHyp` together with the numeric side condition (`c` below about `8190`) is unknown.
2. `μ = 2a` comes from the 2×2-minor term in the transference and is about twice the literature
   exponent; this does not affect the side condition.
3. The reparametrization to `b = a + 1` is a paper remark, not formalized.

`StoppingTime`/`StoppingFarey` status: wall (b) is CLOSED for this project — out of reach without literature access
(WebSearch blocked; Rhin 1987 / Wu–Wang 2014 schemes UNTESTED; [`IrrMeasureReal`: Wu–Wang 2014, J. Number Theory, DOI 10.1016/j.jnt.2014.03.007, 'On the irrationality measure of log 3', concerns log 3, NOT log 3/log 2]), not refuted.  Naive real-segment
Hermite–Padé integrals diverge (`n ≤ 12`, `α ≈ 7.40 > β ≈ 5.72`), which is not evidence against
Rhin-type schemes (their convergence relies on arithmetic denominator reduction).

Classical (Rhin 1987 / Hata transference); not new mathematics; the Goal stays open.
-/

namespace CollatzSearch.Transfer
open CollatzSearch CollatzProof

/-- **Unproved analytic hypothesis** (CONDITIONAL input, not an axiom): a Rhin-type scheme of
linearly independent integer linear forms in `1, log 2, log 3`, coefficients `≤ 2^{c0+an}`,
values `≤ 2^{c0−bn}`, with `a < b`. -/
def SchemeHyp (a b c0 : ℕ) : Prop :=
  a < b ∧ ∀ n : ℕ, ∃ u v w : Z3, det3 u v w ≠ 0 ∧ ∀ x ∈ [u, v, w],
    |form (Real.log 2) (Real.log 3) x| ≤ (2:ℝ)^c0 / 2^(b*n) ∧
    |(x.2.1:ℝ)| ≤ 2^(c0 + a*n) ∧ |(x.2.2:ℝ)| ≤ 2^(c0 + a*n)

/-- Constant bookkeeping: `2^n ≤ 2·2^{2c0+3}·2k ⇒ 8(2^{c0+an})² ≤ 2^{3+2c0+2a(2c0+5)} k^{2a}`. -/
theorem const_bound (a c0 n k : ℕ) (hX : 2^n ≤ 2 * (2^(2*c0+3) * (2*k))) :
    8 * (2^(c0+a*n))^2 ≤ 2^(3 + 2*c0 + 2*a*(2*c0+5)) * k^(2*a) := by
  have e1 : 8 * (2^(c0+a*n))^2 = 2^(2*c0+3) * (2^n)^(2*a) := by
    rw [← pow_mul, ← pow_mul, ← pow_add]; ring_nf
  have e2 : 2 * (2^(2*c0+3) * (2*k)) = 2^(2*c0+5) * k := by ring
  rw [e1]
  calc 2^(2*c0+3) * (2^n)^(2*a) ≤ 2^(2*c0+3) * (2^(2*c0+5) * k)^(2*a) := by
        rw [← e2]; exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hX _)
    _ = 2^(3 + 2*c0 + 2*a*(2*c0+5)) * k^(2*a) := by
        rw [mul_pow, ← pow_mul, ← mul_assoc, ← pow_add]; ring_nf

/-- **`SchemeHyp ⇒ LinFormHyp`** (unconditional implication): for all `k ≥ 1`, `3^k < 2^L`,
`2^L ≤ 2^{3+2c0+2a(2c0+5)} k^{2a} (2^L − 3^k)`, given `SchemeHyp a b c0`. -/
theorem linFormHyp_of_scheme {a b c0 : ℕ} (hS : SchemeHyp a b c0) :
    LinFormHyp 1 (3 + 2*c0 + 2*a*(2*c0+5)) (2*a) := by
  intro k L hk h
  set c := 3 + 2*c0 + 2*a*(2*c0+5) with hc
  by_cases hA : 2 * 3^k ≤ 2^L
  · have h1 : 2^L ≤ 2 * (2^L - 3^k) := by
      generalize 2^L = P at *; generalize 3^k = Q at *; omega
    have h2 : 2 ≤ 2^c := by
      calc 2 = 2^1 := by norm_num
        _ ≤ 2^c := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 1 ≤ k^(2*a) := Nat.one_le_pow _ _ (by omega)
    calc 2^L ≤ 2 * (2^L - 3^k) := h1
      _ ≤ (2^c * k^(2*a)) * (2^L - 3^k) := by
          apply Nat.mul_le_mul_right; nlinarith
  · push Not at hA
    have h34 : 3^k ≤ 4^k := Nat.pow_le_pow_left (by norm_num) k
    have h4 : (4:ℕ)^k = 2^(2*k) := by rw [pow_mul]; norm_num
    have hL2 : L ≤ 2*k := by
      have : 2^L < 2^(2*k+1) := by rw [pow_succ]; omega
      have := (Nat.pow_lt_pow_iff_right (by norm_num)).1 this
      omega
    set M := 2*k with hM
    set X := 2^(2*c0+3) * M with hXdef
    have hX1 : 1 < X := by
      have : 8 ≤ 2^(2*c0+3) := by
        calc 8 = 2^3 := by norm_num
          _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [hXdef]; nlinarith
    set n := Nat.clog 2 X with hn
    have hXn : X ≤ 2^n := Nat.le_pow_clog (by norm_num) X
    have hn0 : 0 < n := Nat.clog_pos (by norm_num) hX1
    have hn2 : 2^n ≤ 2 * X := by
      have := Nat.pow_pred_clog_lt_self (b := 2) (by norm_num) hX1
      rw [← hn] at this
      have e : 2^n = 2 * 2^n.pred := by
        rw [← pow_succ']; exact congrArg _ (Nat.succ_pred_eq_of_pos hn0).symm
      rw [e]; exact Nat.mul_le_mul_left _ this.le
    obtain ⟨hab, hS⟩ := hS
    obtain ⟨u, v, w, hdet, hF⟩ := hS n
    set H : ℝ := 2^(c0 + a*n) with hH
    set ε : ℝ := (2:ℝ)^c0 / 2^(b*n) with hε
    -- smallness
    have hN : 2^(2*c0+3) * M * 2^(a*n) ≤ 2^(b*n) := by
      have hbn : n + a*n ≤ b*n := by nlinarith
      calc 2^(2*c0+3) * M * 2^(a*n) = X * 2^(a*n) := by rw [hXdef]
        _ ≤ 2^n * 2^(a*n) := Nat.mul_le_mul_right _ hXn
        _ = 2^(n + a*n) := by rw [pow_add]
        _ ≤ 2^(b*n) := Nat.pow_le_pow_right (by norm_num) hbn
    have hsmall : 8 * H * (M:ℝ) * ε ≤ 1 := by
      have hpos : (0:ℝ) < 2^(b*n) := by positivity
      have hNR : ((2^(2*c0+3) * M * 2^(a*n) : ℕ) : ℝ) ≤ ((2^(b*n) : ℕ) : ℝ) := by exact_mod_cast hN
      push_cast at hNR
      rw [hH, hε, mul_div_assoc', div_le_one hpos]
      calc (8:ℝ) * 2^(c0 + a*n) * (M:ℝ) * 2^c0 = 2^(2*c0+3) * (M:ℝ) * 2^(a*n) := by ring
        _ ≤ _ := hNR
    have hkR : |((k:ℤ):ℝ)| ≤ (M:ℝ) := by
      rw [Int.cast_natCast, abs_of_nonneg (by positivity)]; rw [hM]; push_cast; linarith
    have hLR : |((L:ℤ):ℝ)| ≤ (M:ℝ) := by
      rw [Int.cast_natCast, abs_of_nonneg (by positivity)]; exact_mod_cast hL2
    have hT := transfer (l2 := Real.log 2) (l3 := Real.log 3) (L := (L:ℤ)) (k := (k:ℤ)) hdet hF
      (by exact_mod_cast hk) hkR hLR hsmall
    rw [Int.cast_natCast, Int.cast_natCast] at hT
    have hx := linForm_pos h
    set x := (L:ℝ) * Real.log 2 - k * Real.log 3 with hxdef
    have habs : |(k:ℝ) * Real.log 3 - L * Real.log 2| = x := by
      rw [abs_sub_comm, abs_of_pos hx]
    rw [habs] at hT
    have hH1 : (1:ℝ) ≤ H := one_le_pow₀ (by norm_num)
    have hHH : (0:ℝ) < 4 * H^2 := by positivity
    have hδx : 1 / (4 * H^2) ≤ x := by rw [div_le_iff₀ hHH]; linarith
    have hδ1 : 1 / (4 * H^2) ≤ 1 := by rw [div_le_iff₀ hHH]; nlinarith
    have hg := gap_of_linForm h (by positivity) hδ1 hδx
    have hD : (0:ℝ) ≤ (2:ℝ)^L - 3^k := by
      have : (3:ℝ)^k < 2^L := by exact_mod_cast h
      linarith
    have hmain : (2:ℝ)^L ≤ 8 * H^2 * ((2:ℝ)^L - 3^k) := by
      have e : (2:ℝ)^L = (2^L * (1 / (4*H^2))) * (4 * H^2) := by field_simp
      rw [e]; nlinarith
    have hcN := const_bound a c0 n k (by rw [← hM, ← hXdef]; exact hn2)
    have hcR : 8 * H^2 ≤ ((2^c * k^(2*a) : ℕ) : ℝ) := by
      rw [hH]; exact_mod_cast hcN
    have hfin : ((2^L : ℕ) : ℝ) ≤ ((2^c * k^(2*a) * (2^L - 3^k) : ℕ) : ℝ) := by
      rw [Nat.cast_mul, Nat.cast_sub h.le]; push_cast
      push_cast at hcR
      calc (2:ℝ)^L ≤ 8 * H^2 * ((2:ℝ)^L - 3^k) := hmain
        _ ≤ _ := mul_le_mul_of_nonneg_right hcR hD
    exact_mod_cast hfin

/-- **CONDITIONAL on the unproved `SchemeHyp a b c0`**, and on the numeric side condition
`8(c + 17μ + 2) ≤ 2^16` for `c = 3+2c0+2a(2c0+5)`, `μ = 2a`: every positive `T`-cycle point
(any phase, any period) whose window has `≤ 2` odd runs is `1` or `2` — for every `k`. -/
theorem few_runs_cycle_trivial_of_scheme {a b c0 : ℕ} (hS : SchemeHyp a b c0)
    (h0 : 8 * ((3 + 2*c0 + 2*a*(2*c0+5)) + 17*(2*a) + 2) ≤ 2^16) {x L : ℕ} (hx : 0 < x)
    (hL : 0 < L) (hc : T^[L] x = x) (hr : oddRuns L x ≤ 2) : x = 1 ∨ x = 2 :=
  few_runs_cycle_trivial_of_linForm (by norm_num) h0 (linFormHyp_of_scheme hS) hx hL hc hr

/-- **Goal-shaped, CONDITIONAL on `SchemeHyp a b c0`** (and the side condition): a positive
`C`-cycle point `n ∉ {1,2,4}` yields an odd `T`-cycle point `m`, `2^17 ≤ m ≤ n`, whose window
has `≥ 3` odd runs. -/
theorem nontrivial_C_cycle_three_runs_of_scheme {a b c0 : ℕ} (hS : SchemeHyp a b c0)
    (h0 : 8 * ((3 + 2*c0 + 2*a*(2*c0+5)) + 17*(2*a) + 2) ≤ 2^16)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2)
    (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 3 ≤ oddRuns L m :=
  nontrivial_C_cycle_three_runs_of_linForm (by norm_num) h0 (linFormHyp_of_scheme hS)
    n hn ℓ hℓ h h1 h2 h4

/-- The side condition is satisfiable for moderate parameters, e.g. `a = 7`, `c0 = 10`
(`c = 373`, `μ = 14`). It fails for large parameters, e.g. `a = 100`, `c0 = 20`. -/
example : 8 * ((3 + 2*10 + 2*7*(2*10+5)) + 17*(2*7) + 2) ≤ 2^16 := by norm_num
example : ¬ 8 * ((3 + 2*20 + 2*100*(2*20+5)) + 17*(2*100) + 2) ≤ 2^16 := by norm_num

end CollatzSearch.Transfer

#print axioms CollatzSearch.Transfer.const_bound
#print axioms CollatzSearch.Transfer.linFormHyp_of_scheme
#print axioms CollatzSearch.Transfer.few_runs_cycle_trivial_of_scheme
#print axioms CollatzSearch.Transfer.nontrivial_C_cycle_three_runs_of_scheme
