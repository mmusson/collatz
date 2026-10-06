import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-!
# Cramer-type transference (wall (b) interface), part 1

Classical (Rhin / Hata style) elimination argument, **no Collatz content**:

* `det3`, Cramer identities `cramer1/2/3`, `det3_pair_ne_zero`: if `det3 u v w ≠ 0` and
  `b ≠ 0` then one of `det3 u v b`, `det3 v w b`, `det3 w u b` is nonzero.
* `elim_identity`, `elim_bound`, `transfer`: three linearly independent integer linear forms
  `x₁ + x₂ λ₂ + x₃ λ₃` that are all `≤ ε` in absolute value, with coefficients `x₂, x₃` of size
  `≤ H`, give `1 ≤ 4 H² |k λ₃ − L λ₂|` for all integers `0 < k`, `|k|,|L| ≤ M` with
  `8 H M ε ≤ 1`.
* `one_sub_exp_neg_ge`, `linForm_pos`, `gap_of_linForm`: the exp/log bridge from a lower
  bound on `L log 2 − k log 3` to a lower bound on `2^L − 3^k`.

All unconditional. Not new mathematics.
-/

namespace CollatzSearch.Transfer

/-- Integer triples `(x₁, x₂, x₃)`. -/
abbrev Z3 := ℤ × ℤ × ℤ

/-- The `3×3` determinant with rows `u, v, w`. -/
def det3 (u v w : Z3) : ℤ :=
  u.1*(v.2.1*w.2.2 - v.2.2*w.2.1) - u.2.1*(v.1*w.2.2 - v.2.2*w.1) + u.2.2*(v.1*w.2.1 - v.2.1*w.1)

example : det3 (1,0,0) (0,1,0) (0,0,1) = 1 := by decide

/-- Cramer identity (first coordinate): `det(u,v,w)·b = Σ det(row replaced by b)·row`. -/
theorem cramer1 (u v w b : Z3) :
    det3 u v w * b.1 = det3 b v w * u.1 + det3 u b w * v.1 + det3 u v b * w.1 := by
  simp only [det3]; ring
/-- Cramer identity (second coordinate). -/
theorem cramer2 (u v w b : Z3) :
    det3 u v w * b.2.1 = det3 b v w * u.2.1 + det3 u b w * v.2.1 + det3 u v b * w.2.1 := by
  simp only [det3]; ring
/-- Cramer identity (third coordinate). -/
theorem cramer3 (u v w b : Z3) :
    det3 u v w * b.2.2 = det3 b v w * u.2.2 + det3 u b w * v.2.2 + det3 u v b * w.2.2 := by
  simp only [det3]; ring

/-- `det3` is invariant under cyclic permutation of rows. -/
theorem det3_cycle (u v w : Z3) : det3 u v w = det3 v w u := by simp only [det3]; ring

/-- If `u, v, w` are linearly independent and `b ≠ 0`, some pair among them together with
`b` is still linearly independent: `det3 u v b`, `det3 v w b` or `det3 w u b` is nonzero. -/
theorem det3_pair_ne_zero {u v w b : Z3} (h : det3 u v w ≠ 0) (hb : b ≠ 0) :
    det3 u v b ≠ 0 ∨ det3 v w b ≠ 0 ∨ det3 w u b ≠ 0 := by
  by_contra hc
  push Not at hc
  obtain ⟨h1, h2, h3⟩ := hc
  have e1 : det3 b v w = det3 v w b := det3_cycle _ _ _
  have e2 : det3 u b w = det3 w u b := by rw [det3_cycle, det3_cycle]
  apply hb
  obtain ⟨b1, b2, b3⟩ := b
  have c1 := cramer1 u v w (b1, b2, b3)
  have c2 := cramer2 u v w (b1, b2, b3)
  have c3 := cramer3 u v w (b1, b2, b3)
  rw [e1, e2, h1, h2, h3] at c1 c2 c3
  simp only [zero_mul, add_zero, mul_eq_zero] at c1 c2 c3
  rw [Prod.mk.injEq, Prod.mk.injEq]
  exact ⟨c1.resolve_left h, c2.resolve_left h, c3.resolve_left h⟩

/-- The real linear form `x₁ + x₂ λ₂ + x₃ λ₃`. -/
def form (l2 l3 : ℝ) (x : Z3) : ℝ := x.1 + x.2.1 * l2 + x.2.2 * l3

/-- Elimination identity: with `b = (0, −L, k)`, `det3 u v b = F(u)(v₂k+v₃L) − F(v)(u₂k+u₃L)
+ (u₂v₃ − v₂u₃)(kλ₃ − Lλ₂)`. -/
theorem elim_identity (l2 l3 : ℝ) (u v : Z3) (L k : ℤ) :
    ((det3 u v (0, -L, k) : ℤ) : ℝ) =
      form l2 l3 u * (v.2.1*k + v.2.2*L) - form l2 l3 v * (u.2.1*k + u.2.2*L)
        + (u.2.1*v.2.2 - v.2.1*u.2.2) * (k*l3 - L*l2) := by
  simp only [det3, form]; push_cast; ring

/-- If `det3 u v (0,−L,k) ≠ 0`, `|F(u)|,|F(v)| ≤ ε`, coefficients `≤ H`, `|k|,|L| ≤ M`,
then `1 ≤ 4HMε + 2H²|kλ₃ − Lλ₂|`. -/
theorem elim_bound {l2 l3 ε H M : ℝ} {u v : Z3} {L k : ℤ} (hd : det3 u v (0,-L,k) ≠ 0)
    (hu : |form l2 l3 u| ≤ ε) (hv : |form l2 l3 v| ≤ ε)
    (hq : |(u.2.1:ℝ)| ≤ H ∧ |(u.2.2:ℝ)| ≤ H ∧ |(v.2.1:ℝ)| ≤ H ∧ |(v.2.2:ℝ)| ≤ H)
    (hk : |(k:ℝ)| ≤ M) (hL : |(L:ℝ)| ≤ M) : 1 ≤ 4*H*M*ε + 2*H^2*|k*l3 - L*l2| := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  have hH : 0 ≤ H := (abs_nonneg _).trans h1
  have hM : 0 ≤ M := (abs_nonneg _).trans hk
  have hε : 0 ≤ ε := (abs_nonneg _).trans hu
  have hone : (1:ℝ) ≤ |((det3 u v (0,-L,k) : ℤ) : ℝ)| := by
    have := Int.one_le_abs hd
    exact_mod_cast this
  rw [elim_identity l2 l3] at hone
  set Fu := form l2 l3 u
  set Fv := form l2 l3 v
  set Λ := (k:ℝ)*l3 - L*l2
  have bA : |(v.2.1:ℝ)*k + v.2.2*L| ≤ 2*H*M := by
    calc _ ≤ |(v.2.1:ℝ)*k| + |(v.2.2:ℝ)*L| := abs_add_le _ _
      _ = |(v.2.1:ℝ)| * |(k:ℝ)| + |(v.2.2:ℝ)| * |(L:ℝ)| := by rw [abs_mul, abs_mul]
      _ ≤ H*M + H*M := by gcongr
      _ = 2*H*M := by ring
  have bB : |(u.2.1:ℝ)*k + u.2.2*L| ≤ 2*H*M := by
    calc _ ≤ |(u.2.1:ℝ)*k| + |(u.2.2:ℝ)*L| := abs_add_le _ _
      _ = |(u.2.1:ℝ)| * |(k:ℝ)| + |(u.2.2:ℝ)| * |(L:ℝ)| := by rw [abs_mul, abs_mul]
      _ ≤ H*M + H*M := by gcongr
      _ = 2*H*M := by ring
  have bC : |(u.2.1:ℝ)*v.2.2 - v.2.1*u.2.2| ≤ 2*H^2 := by
    calc _ ≤ |(u.2.1:ℝ)*v.2.2| + |(v.2.1:ℝ)*u.2.2| := abs_sub _ _
      _ = |(u.2.1:ℝ)| * |(v.2.2:ℝ)| + |(v.2.1:ℝ)| * |(u.2.2:ℝ)| := by rw [abs_mul, abs_mul]
      _ ≤ H*H + H*H := by gcongr
      _ = 2*H^2 := by ring
  calc (1:ℝ) ≤ _ := hone
    _ ≤ |Fu * ((v.2.1:ℝ)*k + v.2.2*L) - Fv * ((u.2.1:ℝ)*k + u.2.2*L)|
          + |((u.2.1:ℝ)*v.2.2 - v.2.1*u.2.2) * Λ| := abs_add_le _ _
    _ ≤ (|Fu * ((v.2.1:ℝ)*k + v.2.2*L)| + |Fv * ((u.2.1:ℝ)*k + u.2.2*L)|)
          + |((u.2.1:ℝ)*v.2.2 - v.2.1*u.2.2) * Λ| := by gcongr; exact abs_sub _ _
    _ = (|Fu| * |(v.2.1:ℝ)*k + v.2.2*L| + |Fv| * |(u.2.1:ℝ)*k + u.2.2*L|)
          + |(u.2.1:ℝ)*v.2.2 - v.2.1*u.2.2| * |Λ| := by rw [abs_mul, abs_mul, abs_mul]
    _ ≤ (ε * (2*H*M) + ε * (2*H*M)) + 2*H^2 * |Λ| := by gcongr
    _ = 4*H*M*ε + 2*H^2*|Λ| := by ring

/-- **Transfer theorem.** Three linearly independent integer forms with `|F| ≤ ε` and
`|x₂|,|x₃| ≤ H`, and integers `0 < k`, `|k|,|L| ≤ M` with `8HMε ≤ 1`, give
`1 ≤ 4H²|kλ₃ − Lλ₂|`. -/
theorem transfer {l2 l3 ε H M : ℝ} {u v w : Z3} {L k : ℤ} (hdet : det3 u v w ≠ 0)
    (hF : ∀ x ∈ [u,v,w], |form l2 l3 x| ≤ ε ∧ |(x.2.1:ℝ)| ≤ H ∧ |(x.2.2:ℝ)| ≤ H)
    (hk0 : 0 < k) (hk : |(k:ℝ)| ≤ M) (hL : |(L:ℝ)| ≤ M) (hsmall : 8*H*M*ε ≤ 1) :
    1 ≤ 4*H^2*|k*l3 - L*l2| := by
  have hb : ((0, -L, k) : Z3) ≠ 0 := by
    intro h
    have : k = 0 := congrArg (fun x : Z3 => x.2.2) h
    omega
  obtain ⟨Fu, Hu1, Hu2⟩ := hF u (by simp)
  obtain ⟨Fv, Hv1, Hv2⟩ := hF v (by simp)
  obtain ⟨Fw, Hw1, Hw2⟩ := hF w (by simp)
  have key : 1 ≤ 4*H*M*ε + 2*H^2*|k*l3 - L*l2| := by
    rcases det3_pair_ne_zero hdet hb with h | h | h
    · exact elim_bound h Fu Fv ⟨Hu1, Hu2, Hv1, Hv2⟩ hk hL
    · exact elim_bound h Fv Fw ⟨Hv1, Hv2, Hw1, Hw2⟩ hk hL
    · exact elim_bound h Fw Fu ⟨Hw1, Hw2, Hu1, Hu2⟩ hk hL
  nlinarith

/-! ## T2: exp/log bridge -/

/-- `0 < δ ≤ 1`, `δ ≤ x` ⇒ `δ/2 ≤ 1 − e^{−x}`. -/
theorem one_sub_exp_neg_ge {x δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hx : δ ≤ x) :
    δ/2 ≤ 1 - Real.exp (-x) := by
  have h1 : 1 + δ ≤ Real.exp δ := by linarith [Real.add_one_le_exp δ]
  have h2 : Real.exp (-x) ≤ Real.exp (-δ) := Real.exp_le_exp.2 (by linarith)
  have h3 : Real.exp (-δ) * Real.exp δ = 1 := by rw [← Real.exp_add]; simp
  have hpos : 0 < Real.exp (-δ) := Real.exp_pos _
  have h4 : Real.exp (-δ) * (1 + δ) ≤ 1 := by nlinarith
  nlinarith

/-- `3^k < 2^L` ⇒ `L log 2 − k log 3 > 0`. -/
theorem linForm_pos {k L : ℕ} (h : 3^k < 2^L) : 0 < (L:ℝ) * Real.log 2 - k * Real.log 3 := by
  have hR : (3:ℝ)^k < 2^L := by exact_mod_cast h
  have := Real.log_lt_log (by positivity) hR
  rw [Real.log_pow, Real.log_pow] at this
  linarith

/-- `3^k < 2^L`, `0 < δ ≤ 1`, `δ ≤ L log 2 − k log 3` ⇒ `2^L δ ≤ 2(2^L − 3^k)` (in `ℝ`). -/
theorem gap_of_linForm {k L : ℕ} (_h : 3^k < 2^L) {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hx : δ ≤ (L:ℝ) * Real.log 2 - k * Real.log 3) :
    (2:ℝ)^L * δ ≤ 2 * ((2:ℝ)^L - 3^k) := by
  have h2 : (0:ℝ) < 2^L := by positivity
  have h3 : (0:ℝ) < 3^k := by positivity
  set y := (3:ℝ)^k / 2^L with hy
  have hypos : 0 < y := div_pos h3 h2
  have hlog : Real.log y = -((L:ℝ) * Real.log 2 - k * Real.log 3) := by
    rw [hy, Real.log_div h3.ne' h2.ne', Real.log_pow, Real.log_pow]; ring
  have hyexp : y = Real.exp (-((L:ℝ) * Real.log 2 - k * Real.log 3)) := by
    rw [← hlog, Real.exp_log hypos]
  have hb := one_sub_exp_neg_ge hδ hδ1 hx
  rw [← hyexp] at hb
  have e : (3:ℝ)^k = 2^L * y := by rw [hy]; field_simp
  rw [e]
  nlinarith

end CollatzSearch.Transfer

#print axioms CollatzSearch.Transfer.det3_pair_ne_zero
#print axioms CollatzSearch.Transfer.elim_identity
#print axioms CollatzSearch.Transfer.elim_bound
#print axioms CollatzSearch.Transfer.transfer
#print axioms CollatzSearch.Transfer.one_sub_exp_neg_ge
#print axioms CollatzSearch.Transfer.linForm_pos
#print axioms CollatzSearch.Transfer.gap_of_linForm
