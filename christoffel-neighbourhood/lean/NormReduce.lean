import NormGoal
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic

/-!
# one-move Christoffel words reduce to two trinomials in `ZMod q`

Setting: `r ≥ 2`, `gcd(A, r) = 1`, `3^r + 1 < 2^A`, `q = 2^A - 3^r`.

* `exists_g`, `g_unique`: there is a unique `g ∈ ZMod q` with `g^r = 2` and `g^A = 3`.
* `knight_identity`: `(g - 1) · B(chr r A) = g^((A-1)(r-1))` in `ZMod q`; hence `knight`:
  `q ∤ B(chr r A)` (Knight 2026's Christoffel case; the same short argument via a distinguished
  unit appears in Mghirbi 2026 and, prime by prime, in Lebel 2026).
* `reduce`: if `v` is one cyclic swap or one slide from `chr r A` and `q ∣ B(v)`, then
  `g^(p+1) - g^p + 1 = 0` for some `1 ≤ p ≤ r-1` (Type I) or `g^e - g + 1 = 0` for some
  `2 ≤ e ≤ r` (Type II); when `A < 2r`, additionally `p + 1 ≤ A - r` resp. `e ≤ A - r`.

The proof: every Christoffel term is `G g^(r-1-(iA mod r))`, `i ↦ iA mod r` is a bijection, and
each move changes one partial sum by `±1` or all partial sums `1..r-1` by `±1`.
-/

namespace CollatzSearch.NormReduce
open CollatzSearch.NormGoal Finset

/-! ### L0: arithmetic facts -/

theorem r_lt_A {r A : ℕ} (hq : 3 ^ r + 1 < 2 ^ A) : r < A := by
  by_contra h
  simp only [not_le, not_lt] at h
  have : 2 ^ A ≤ 3 ^ r :=
    (Nat.pow_le_pow_right (by norm_num) h).trans (Nat.pow_le_pow_left (by norm_num) r)
  omega

theorem three_r_le_two_A {r A : ℕ} (hq : 3 ^ r + 1 < 2 ^ A) : 3 * r ≤ 2 * A := by
  by_contra h
  simp only [not_le, not_lt] at h
  have h1 : 2 ^ (2 * A) ≤ 2 ^ (3 * r) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 2 ^ (2 * A) = (2 ^ A) ^ 2 := by rw [pow_mul']
  have h3 : 2 ^ (3 * r) = 8 ^ r := by rw [pow_mul]; norm_num
  have h4 : 8 ^ r ≤ 9 ^ r := Nat.pow_le_pow_left (by norm_num) r
  have h5 : (9:ℕ) ^ r = (3 ^ r) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
  have h6 : (3 ^ r) ^ 2 < (2 ^ A) ^ 2 := Nat.pow_lt_pow_left (by omega) (by norm_num)
  omega

theorem q_odd {r A : ℕ} (hq : 3 ^ r + 1 < 2 ^ A) : (2 ^ A - 3 ^ r) % 2 = 1 := by
  have hA : 1 ≤ A := by
    rcases Nat.eq_zero_or_pos A with h | h
    · subst h; simp at hq
    · exact h
  have h2 : 2 ^ A % 2 = 0 := by
    obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
    rw [pow_succ]; simp
  have h3 : 3 ^ r % 2 = 1 := by rw [Nat.pow_mod]; simp
  omega

theorem coprime_two {r A : ℕ} (hq : 3 ^ r + 1 < 2 ^ A) : Nat.Coprime 2 (2 ^ A - 3 ^ r) := by
  rw [Nat.coprime_two_left]; exact Nat.odd_iff.mpr (q_odd hq)

theorem coprime_three {r A : ℕ} (hr : 0 < r) (hq : 3 ^ r + 1 < 2 ^ A) :
    Nat.Coprime 3 (2 ^ A - 3 ^ r) := by
  rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
  intro h
  have h1 : 3 ∣ 3 ^ r := dvd_pow_self 3 (by omega)
  have : 3 ∣ 2 ^ A := by
    have := Nat.sub_add_cancel (show 3 ^ r ≤ 2 ^ A by omega)
    rw [← this]; exact dvd_add h h1
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three this
  omega

theorem one_lt_q {r A : ℕ} (hq : 3 ^ r + 1 < 2 ^ A) : 1 < 2 ^ A - 3 ^ r := by omega

/-- In `ZMod q`, `2^A = 3^r`. -/
theorem two_pow_eq {r A : ℕ} (hq : 3 ^ r + 1 < 2 ^ A) :
    (2 : ZMod (2 ^ A - 3 ^ r)) ^ A = 3 ^ r := by
  have h : ((2 ^ A - 3 ^ r : ℕ) : ZMod (2 ^ A - 3 ^ r)) = 0 := ZMod.natCast_self _
  rw [Nat.cast_sub (by omega)] at h
  push_cast at h
  exact sub_eq_zero.mp h

theorem isUnit_two {r A : ℕ} (hq : 3 ^ r + 1 < 2 ^ A) : IsUnit (2 : ZMod (2 ^ A - 3 ^ r)) := by
  have := (ZMod.unitOfCoprime 2 (coprime_two hq)).isUnit
  simpa using this

theorem isUnit_three {r A : ℕ} (hr : 0 < r) (hq : 3 ^ r + 1 < 2 ^ A) :
    IsUnit (3 : ZMod (2 ^ A - 3 ^ r)) := by
  have := (ZMod.unitOfCoprime 3 (coprime_three hr hq)).isUnit
  simpa using this

theorem nontrivial_q {r A : ℕ} (hq : 3 ^ r + 1 < 2 ^ A) : Nontrivial (ZMod (2 ^ A - 3 ^ r)) :=
  ZMod.nontrivial_iff.mpr (by omega)

/-! ### L1: the generator `g` -/

theorem exists_uk {r A : ℕ} (hA : 2 ≤ A) (hcop : Nat.Coprime A r) : ∃ u k, r * u = A * k + 1 := by
  obtain ⟨u, _, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop.symm (by omega)
  exact ⟨u, r * u / A, by have := Nat.div_add_mod (r * u) A; rw [hu] at this; linarith⟩

/-- **Existence of `g`.** -/
theorem exists_g {r A : ℕ} (hr : 1 ≤ r) (hcop : Nat.Coprime A r) (hq : 3 ^ r + 1 < 2 ^ A) :
    ∃ g : ZMod (2 ^ A - 3 ^ r), g ^ r = 2 ∧ g ^ A = 3 := by
  have hA : 2 ≤ A := by have := r_lt_A hq; omega
  obtain ⟨u, k, huk⟩ := exists_uk hA hcop
  obtain ⟨t, ht⟩ := (isUnit_three hr hq).exists_right_inv
  have h2A := two_pow_eq hq
  refine ⟨2 ^ u * t ^ k, ?_, ?_⟩
  · rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm u r, huk, pow_succ, pow_mul, h2A, ← pow_mul,
      mul_comm k r]
    calc (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r * k) * 2 * t ^ (r * k)
        = 2 * (3 * t) ^ (r * k) := by ring
      _ = 2 := by rw [ht]; simp
  · rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm u A, pow_mul, h2A, ← pow_mul, huk, pow_succ,
      mul_comm k A]
    calc (3 : ZMod (2 ^ A - 3 ^ r)) ^ (A * k) * 3 * t ^ (A * k)
        = 3 * (3 * t) ^ (A * k) := by ring
      _ = 3 := by rw [ht]; simp

/-- **Uniqueness of `g`.** -/
theorem g_unique {r A : ℕ} (hr : 1 ≤ r) (hcop : Nat.Coprime A r) (hq : 3 ^ r + 1 < 2 ^ A)
    {g g' : ZMod (2 ^ A - 3 ^ r)} (h : g ^ r = 2) (h' : g ^ A = 3)
    (k : g' ^ r = 2) (k' : g' ^ A = 3) : g = g' := by
  have hA : 2 ≤ A := by have := r_lt_A hq; omega
  obtain ⟨u, m, hum⟩ := exists_uk hA hcop
  have e1 : g ^ (r * u) = g ^ (A * m + 1) := by rw [hum]
  have e2 : g' ^ (r * u) = g' ^ (A * m + 1) := by rw [hum]
  rw [pow_mul, h, pow_succ, pow_mul, h'] at e1
  rw [pow_mul, k, pow_succ, pow_mul, k'] at e2
  have hu : IsUnit ((3 : ZMod (2 ^ A - 3 ^ r)) ^ m) := (isUnit_three hr hq).pow m
  exact hu.mul_left_cancel (e1.symm.trans e2)

/-! ### L2: the Christoffel word -/

theorem psum_chr {r A : ℕ} (j : ℕ) : psum (chr r A) j = j * A / r := by
  induction j with
  | zero => simp [psum]
  | succ j ih =>
    rw [psum, sum_range_succ, ← psum, ih, chr]
    have : j * A / r ≤ (j + 1) * A / r := Nat.div_le_div_right (by nlinarith)
    omega

theorem chr_eq {r A : ℕ} (hr : 0 < r) (j : ℕ) :
    chr r A j = A / r + (if r ≤ j * A % r + A % r then 1 else 0) := by
  rw [chr, add_mul, one_mul]
  split_ifs with h
  · rw [Nat.add_div_eq_of_le_mod_add_mod h hr, add_assoc, Nat.add_sub_cancel_left]
  · rw [Nat.add_div_eq_of_add_mod_lt (by omega), Nat.add_sub_cancel_left, add_zero]

theorem mod_lt_two {x r : ℕ} (h : x < 2 * r) : x % r = if r ≤ x then x - r else x := by
  split_ifs with h1
  · rw [Nat.mod_eq_sub_mod h1, Nat.mod_eq_of_lt (by omega)]
  · exact Nat.mod_eq_of_lt (by omega)

theorem mod_succ {r A : ℕ} (hr : 0 < r) (j : ℕ) :
    ((j + 1) * A) % r =
      if r ≤ j * A % r + A % r then j * A % r + A % r - r else j * A % r + A % r := by
  rw [add_mul, one_mul, Nat.add_mod]
  exact mod_lt_two (by have := Nat.mod_lt (j * A) hr; have := Nat.mod_lt A hr; omega)

theorem rho_pos {r A : ℕ} (hr : 2 ≤ r) (hcop : Nat.Coprime A r) : 0 < A % r := by
  by_contra h
  have h0 : A % r = 0 := by omega
  have : r ∣ A := Nat.dvd_of_mod_eq_zero h0
  have := Nat.Coprime.eq_one_of_dvd hcop.symm this
  omega

theorem chr_zero {r A : ℕ} (hr : 0 < r) : chr r A 0 = A / r := by
  rw [chr_eq hr]; simp [Nat.mod_lt A hr]

theorem chr_last {r A : ℕ} (hr : 2 ≤ r) (hcop : Nat.Coprime A r) :
    chr r A (r - 1) = A / r + 1 := by
  have hρ := rho_pos hr hcop
  have hm : (r - 1) * A % r + A % r = r := by
    have h1 : ((r - 1) * A + A) % r = 0 := by
      have : (r - 1) * A + A = r * A := by
        obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
        simp; ring
      rw [this]; simp
    rw [Nat.add_mod] at h1
    have := Nat.mod_lt ((r - 1) * A) (by omega : 0 < r)
    have := Nat.mod_lt A (by omega : 0 < r)
    rw [mod_lt_two (by omega)] at h1
    split_ifs at h1 <;> omega
  rw [chr_eq (by omega), hm]; simp

/-- `j ↦ (j*A) % r` is injective on `range r`. -/
theorem mod_inj {r A : ℕ} (hcop : Nat.Coprime A r) {i j : ℕ} (hi : i < r) (hj : j < r)
    (h : i * A % r = j * A % r) : i = j := by
  have h1 : i * A ≡ j * A [MOD r] := h
  have h2 : i ≡ j [MOD r] := Nat.ModEq.cancel_right_of_coprime (by
    rw [Nat.gcd_comm]; exact hcop) h1
  unfold Nat.ModEq at h2
  rwa [Nat.mod_eq_of_lt hi, Nat.mod_eq_of_lt hj] at h2

/-! ### L3: the Knight identity -/

section G
variable {r A : ℕ}

/-- Each Christoffel term in `ZMod q` is `G * g^(r-1-m_i)`. -/
theorem term_eq {R : Type*} [CommMonoid R] {g : R} (two three : R) (h2 : g ^ r = two)
    (h3 : g ^ A = three) {i : ℕ} (hi : i < r) (hA : 1 ≤ A) :
    three ^ (r - 1 - i) * two ^ (i * A / r) = g ^ ((A - 1) * (r - 1)) * g ^ (r - 1 - i * A % r) := by
  rw [← h2, ← h3, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
  congr 1
  have hd := Nat.div_add_mod (i * A) r
  have hm := Nat.mod_lt (i * A) (show 0 < r by omega)
  set D := i * A / r
  set m := i * A % r
  have : A * (r - 1 - i) + A * i = A * (r - 1) := by
    rw [← mul_add]; congr 1; omega
  have h4 : (A - 1) * (r - 1) + (r - 1) = A * (r - 1) := by
    obtain ⟨B, rfl⟩ : ∃ B, A = B + 1 := ⟨A - 1, by omega⟩
    simp; ring
  have h5 : r * D + m = A * i := by rw [hd]; ring
  omega

theorem sum_reindex {M : Type*} [AddCommMonoid M] (hcop : Nat.Coprime A r) (f : ℕ → M) :
    ∑ i ∈ range r, f (r - 1 - i * A % r) = ∑ t ∈ range r, f t := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; simp
  have hinj : Set.InjOn (fun i => r - 1 - i * A % r) (range r) := by
    intro i hi j hj hij
    simp only [coe_range, Set.mem_Iio] at hi hj hij
    have := Nat.mod_lt (i * A) hr
    have := Nat.mod_lt (j * A) hr
    exact mod_inj hcop hi hj (by omega)
  have himg : (range r).image (fun i => r - 1 - i * A % r) = range r := by
    apply eq_of_subset_of_card_le
    · intro x hx
      simp only [mem_image, mem_range] at hx ⊢
      obtain ⟨i, _, rfl⟩ := hx
      omega
    · rw [card_image_of_injOn hinj]
  rw [← sum_image (f := f) hinj, himg]

end G


/-! ### Casting `Bnum` and partial-sum perturbations -/

theorem cast_Bnum {R : Type*} [CommSemiring R] (r : ℕ) (v : ℕ → ℕ) :
    (Bnum r v : R) = ∑ i ∈ range r, (3 : R) ^ (r - 1 - i) * 2 ^ psum v i := by
  simp [Bnum]

theorem cast_psum (v : ℕ → ℕ) (i : ℕ) : (psum v i : ℤ) = ∑ l ∈ range i, (v l : ℤ) := by
  simp [psum]

/-- One-point perturbation of a finite sum. -/
theorem sum_perturb1 {R : Type*} [AddCommMonoid R] {s : Finset ℕ} {i0 : ℕ} (hi0 : i0 ∈ s)
    (F F' : ℕ → R) (h : ∀ i ∈ s, i ≠ i0 → F' i = F i) :
    ∑ i ∈ s, F' i + F i0 = ∑ i ∈ s, F i + F' i0 := by
  rw [← add_sum_erase s F' hi0, ← add_sum_erase s F hi0,
    sum_congr rfl (fun i hi => h i (mem_of_mem_erase hi) (ne_of_mem_erase hi))]
  abel

/-- Doubling every term but the `0`-th. -/
theorem sum_perturbW {R : Type*} [CommSemiring R] {s : Finset ℕ} (h0 : 0 ∈ s) (F F' : ℕ → R)
    (hF0 : F' 0 = F 0) (h : ∀ i ∈ s, i ≠ 0 → F' i = 2 * F i) :
    ∑ i ∈ s, F' i + F 0 = 2 * ∑ i ∈ s, F i := by
  rw [← add_sum_erase s F' h0, ← add_sum_erase s F h0,
    sum_congr rfl (fun i hi => h i (mem_of_mem_erase hi) (ne_of_mem_erase hi)), ← mul_sum, hF0]
  ring

theorem psum_slide {w : ℕ → ℕ} {j k : ℕ} (hw : 1 ≤ w j) (hkj : k ≠ j) (i : ℕ) :
    (psum (slide w j k) i : ℤ) + (if j < i then 1 else 0) = psum w i + (if k < i then 1 else 0) := by
  have key : ∀ l, (slide w j k l : ℤ) + (if l = j then 1 else 0) =
      w l + (if l = k then 1 else 0) := by
    intro l
    unfold slide
    by_cases h1 : l = j
    · subst h1; simp [hkj.symm]; omega
    · by_cases h2 : l = k
      · subst h2; simp [h1]
      · simp [h1, h2]
  rw [cast_psum, cast_psum]
  have := sum_congr (s₁ := range i) rfl (fun l _ => key l)
  simp only [sum_add_distrib, sum_ite_eq', mem_range] at this
  exact this

theorem cswap_ne {r j : ℕ} (hr : 2 ≤ r) (hj : j < r) : (j + 1) % r ≠ j := by
  by_cases h : j + 1 < r
  · rw [Nat.mod_eq_of_lt h]; omega
  · have : j + 1 = r := by omega
    rw [this, Nat.mod_self]; omega

theorem psum_cswap {r : ℕ} {w : ℕ → ℕ} {j : ℕ} (hr : 2 ≤ r) (hj : j < r) (i : ℕ) :
    (psum (cswap r w j) i : ℤ) + (if j < i then (w j : ℤ) else 0) +
      (if (j + 1) % r < i then (w ((j + 1) % r) : ℤ) else 0) =
    psum w i + (if j < i then (w ((j + 1) % r) : ℤ) else 0) +
      (if (j + 1) % r < i then (w j : ℤ) else 0) := by
  have hne := cswap_ne hr hj
  have key : ∀ l, (cswap r w j l : ℤ) + (if l = j then (w j : ℤ) else 0) +
      (if l = (j + 1) % r then (w ((j + 1) % r) : ℤ) else 0) =
      w l + (if l = j then (w ((j + 1) % r) : ℤ) else 0) +
      (if l = (j + 1) % r then (w j : ℤ) else 0) := by
    intro l
    unfold cswap
    by_cases h1 : l = j
    · subst h1; simp [hne.symm]; ring
    · by_cases h2 : l = (j + 1) % r
      · subst h2; simp [h1]; ring
      · simp [h1, h2]
  rw [cast_psum, cast_psum]
  have := sum_congr (s₁ := range i) rfl (fun l _ => key l)
  simp only [sum_add_distrib, sum_ite_eq', mem_range] at this
  exact this

/-! ### L3: the Knight identity -/

theorem term_chr {r A : ℕ} {R : Type*} [CommMonoid R] {g two three : R} (h2 : g ^ r = two)
    (h3 : g ^ A = three) (hA : 1 ≤ A) {i : ℕ} (hi : i < r) :
    three ^ (r - 1 - i) * two ^ (psum (chr r A) i) =
      g ^ ((A - 1) * (r - 1)) * g ^ (r - 1 - i * A % r) := by
  rw [psum_chr]; exact term_eq two three h2 h3 hi hA

/-- **Knight identity** (cf. Mghirbi 2026, Lebel 2026; gives Knight 2026). In `ZMod q`,
`(g - 1) · B(chr) = g^((A-1)(r-1))`. -/
theorem knight_identity {r A : ℕ} (hr : 2 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) {g : ZMod (2 ^ A - 3 ^ r)} (h2 : g ^ r = 2) (h3 : g ^ A = 3) :
    (g - 1) * (Bnum r (chr r A) : ZMod (2 ^ A - 3 ^ r)) = g ^ ((A - 1) * (r - 1)) := by
  have hA : 1 ≤ A := by have := r_lt_A hq; omega
  rw [cast_Bnum, sum_congr rfl (fun i hi => term_chr h2 h3 hA (mem_range.mp hi)), ← mul_sum,
    sum_reindex hcop (fun t => g ^ t)]
  have := geom_sum_mul g r
  rw [h2] at this
  linear_combination g ^ ((A - 1) * (r - 1)) * this

theorem isUnit_g {r A : ℕ} (hr : 1 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) {g : ZMod (2 ^ A - 3 ^ r)}
    (h2 : g ^ r = 2) : IsUnit g := by
  have := isUnit_two hq
  rw [← h2, isUnit_pow_iff (by omega)] at this
  exact this

/-- **Corollary (Knight 2026).** `q ∤ B(chr)`. -/
theorem knight {r A : ℕ} (hr : 2 ≤ r) (hcop : Nat.Coprime A r) (hq : 3 ^ r + 1 < 2 ^ A) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r (chr r A) := by
  intro hd
  have := nontrivial_q hq
  obtain ⟨g, h2, h3⟩ := exists_g (by omega) hcop hq
  have hK := knight_identity hr hcop hq h2 h3
  rw [(ZMod.natCast_eq_zero_iff _ _).mpr hd, mul_zero] at hK
  exact ((isUnit_g (by omega) hq h2).pow ((A - 1) * (r - 1))).ne_zero hK.symm

/-! ### L4: the main reduction -/

/-- **Reduction to two trinomials.** If `v` is one move from the Christoffel word and
`q ∣ B(v)`, then at the unique `g` (`g^r = 2`, `g^A = 3` in `ZMod q`) either
`g^(p+1) - g^p + 1 = 0` (Type I, `1 ≤ p ≤ r-1`) or `g^e - g + 1 = 0` (Type II, `2 ≤ e ≤ r`);
when `A < 2r` moreover `p + 1 ≤ A - r` resp. `e ≤ A - r`. -/
theorem reduce {r A : ℕ} (hr : 2 ≤ r) (hcop : Nat.Coprime A r) (hq : 3 ^ r + 1 < 2 ^ A)
    {g : ZMod (2 ^ A - 3 ^ r)} (h2 : g ^ r = 2) (h3 : g ^ A = 3) {v : ℕ → ℕ}
    (hv : OneMove r (chr r A) v) (hdiv : (2 ^ A - 3 ^ r) ∣ Bnum r v) :
    (∃ p, 1 ≤ p ∧ p + 1 ≤ r ∧ (A < 2 * r → p + r + 1 ≤ A) ∧ g ^ (p + 1) - g ^ p + 1 = 0) ∨
    (∃ e, 2 ≤ e ∧ e ≤ r ∧ (A < 2 * r → e + r ≤ A) ∧ g ^ e - g + 1 = 0) := by
  have hnt := nontrivial_q hq
  have hr0 : 0 < r := by omega
  have hAr := r_lt_A hq
  have h32 := three_r_le_two_A hq
  have hρ := rho_pos hr hcop
  have hgu := isUnit_g (by omega) hq h2
  have hGu : IsUnit (g ^ ((A - 1) * (r - 1))) := hgu.pow _
  have hK := knight_identity hr hcop hq h2 h3
  have hBv : (Bnum r v : ZMod (2 ^ A - 3 ^ r)) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hdiv
  rw [cast_Bnum] at hBv
  have hBw := cast_Bnum (R := ZMod (2 ^ A - 3 ^ r)) r (chr r A)
  have hτ : ∀ i < r, (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum (chr r A) i =
      g ^ ((A - 1) * (r - 1)) * g ^ (r - 1 - i * A % r) :=
    fun i hi => term_chr h2 h3 (by omega) hi
  have hsmall : A < 2 * r → A / r = 1 ∧ A % r = A - r := by
    intro h
    have h1 : A / r = 1 := Nat.div_eq_of_lt_le (by omega) (by omega)
    have := Nat.div_add_mod A r
    rw [h1] at this
    exact ⟨h1, by omega⟩
  set G := g ^ ((A - 1) * (r - 1)) with hG
  -- the five perturbation cases
  have case0 : (∀ i < r, psum v i = psum (chr r A) i) → False := by
    intro h
    have : (Bnum r (chr r A) : ZMod (2 ^ A - 3 ^ r)) = 0 := by
      rw [hBw, ← hBv]
      exact sum_congr rfl (fun i hi => by rw [h i (mem_range.mp hi)])
    rw [this, mul_zero] at hK
    exact hGu.ne_zero hK.symm
  have caseP : ∀ i0, i0 < r → (∀ i < r, i ≠ i0 → psum v i = psum (chr r A) i) →
      psum v i0 = psum (chr r A) i0 + 1 →
      G * (g ^ (r - 1 - i0 * A % r + 1) - g ^ (r - 1 - i0 * A % r) + 1) = 0 := by
    intro i0 hi0 hne heq
    have := sum_perturb1 (s := range r) (mem_range.mpr hi0)
      (fun i => (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum (chr r A) i)
      (fun i => (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum v i)
      (fun i hi hi' => by rw [hne i (mem_range.mp hi) hi'])
    have e1 : (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i0) * 2 ^ psum v i0 =
        2 * ((3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i0) * 2 ^ psum (chr r A) i0) := by
      rw [heq, pow_succ]; ring
    rw [hBv, e1, hτ i0 hi0, ← hBw] at this
    linear_combination (-(g - 1)) * this - hK
  have caseM : ∀ i0, i0 < r → (∀ i < r, i ≠ i0 → psum v i = psum (chr r A) i) →
      psum v i0 + 1 = psum (chr r A) i0 →
      G * g ^ (r - 1 - i0 * A % r) * (g ^ (i0 * A % r + 1) - g + 1) = 0 := by
    intro i0 hi0 hne heq
    have := sum_perturb1 (s := range r) (mem_range.mpr hi0)
      (fun i => (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum (chr r A) i)
      (fun i => (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum v i)
      (fun i hi hi' => by rw [hne i (mem_range.mp hi) hi'])
    have e1 : (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i0) * 2 ^ psum (chr r A) i0 =
        2 * ((3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i0) * 2 ^ psum v i0) := by
      rw [← heq, pow_succ]; ring
    have hτ0 := hτ i0 hi0
    rw [hBv, ← hBw] at this
    have hm := Nat.mod_lt (i0 * A) hr0
    have hpow : g ^ r = g ^ (r - 1 - i0 * A % r) * g ^ (i0 * A % r + 1) := by
      rw [← pow_add]; congr 1; omega
    have E3 : G * g ^ (r - 1 - i0 * A % r) = 2 * (Bnum r (chr r A) : ZMod (2 ^ A - 3 ^ r)) := by
      linear_combination -hτ0 - e1 + 2 * this
    linear_combination (-G) * hpow + G * h2 - (g - 1) * E3 - 2 * hK
  have caseWp : (∀ i < r, i ≠ 0 → psum v i = psum (chr r A) i + 1) → False := by
    intro h
    have := sum_perturbW (s := range r) (mem_range.mpr hr0)
      (fun i => (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum (chr r A) i)
      (fun i => (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum v i)
      (by simp [psum])
      (fun i hi hi' => by rw [h i (mem_range.mp hi) hi', pow_succ]; ring)
    have hτ0 := hτ 0 hr0
    simp only [zero_mul, Nat.zero_mod, Nat.sub_zero] at hτ0
    rw [hBv, ← hBw, Nat.sub_zero, hτ0] at this
    have hpow : g ^ r = g ^ (r - 1) * g := by rw [← pow_succ]; congr 1; omega
    have : G * g ^ (r - 1) = 0 := by
      linear_combination (-G) * hpow + G * h2 - (g - 1) * this - 2 * hK
    exact (hGu.mul (hgu.pow _)).ne_zero this
  have caseWm : (∀ i < r, i ≠ 0 → psum v i + 1 = psum (chr r A) i) →
      G * (g ^ r - g ^ (r - 1) + 1) = 0 := by
    intro h
    have := sum_perturbW (s := range r) (mem_range.mpr hr0)
      (fun i => (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum v i)
      (fun i => (3 : ZMod (2 ^ A - 3 ^ r)) ^ (r - 1 - i) * 2 ^ psum (chr r A) i)
      (by simp [psum])
      (fun i hi hi' => by rw [← h i (mem_range.mp hi) hi', pow_succ]; ring)
    have hτ0 := hτ 0 hr0
    simp only [zero_mul, Nat.zero_mod, Nat.sub_zero] at hτ0
    have hp0 : psum v 0 = psum (chr r A) 0 := by simp [psum]
    rw [hBv, ← hBw, hp0, Nat.sub_zero, hτ0] at this
    have hpow : g ^ r = g ^ (r - 1) * g := by rw [← pow_succ]; congr 1; omega
    linear_combination G * hpow + (g - 1) * this - hK
  -- turning the cases into the two types
  have typeI : ∀ i0, i0 < r → (A < 2 * r → r ≤ i0 * A % r + A % r) →
      (∀ i < r, i ≠ i0 → psum v i = psum (chr r A) i) →
      psum v i0 = psum (chr r A) i0 + 1 →
      ∃ p, 1 ≤ p ∧ p + 1 ≤ r ∧ (A < 2 * r → p + r + 1 ≤ A) ∧ g ^ (p + 1) - g ^ p + 1 = 0 := by
    intro i0 hi0 hrange hne heq
    have hx := hGu.mul_right_eq_zero.mp (caseP i0 hi0 hne heq)
    have hm := Nat.mod_lt (i0 * A) hr0
    refine ⟨r - 1 - i0 * A % r, ?_, by omega, fun h => ?_, hx⟩
    · by_contra hp
      have hp0 : r - 1 - i0 * A % r = 0 := by omega
      rw [hp0] at hx
      simp at hx
      exact hgu.ne_zero hx
    · have := hsmall h; have := hrange h; omega
  have typeII : ∀ i0, i0 < r → (A < 2 * r → i0 * A % r + 1 ≤ A % r) →
      (∀ i < r, i ≠ i0 → psum v i = psum (chr r A) i) →
      psum v i0 + 1 = psum (chr r A) i0 →
      ∃ e, 2 ≤ e ∧ e ≤ r ∧ (A < 2 * r → e + r ≤ A) ∧ g ^ e - g + 1 = 0 := by
    intro i0 hi0 hrange hne heq
    have hx := (hGu.mul (hgu.pow _)).mul_right_eq_zero.mp (caseM i0 hi0 hne heq)
    have hm := Nat.mod_lt (i0 * A) hr0
    refine ⟨i0 * A % r + 1, ?_, by omega, fun h => ?_, hx⟩
    · by_contra he
      have he0 : i0 * A % r = 0 := by omega
      rw [he0] at hx
      simp at hx
    · have := hsmall h; have := hrange h; omega
  -- the move analysis
  have hc := fun j => chr_eq (A := A) hr0 j
  rcases hv with ⟨j, hj, rfl⟩ | ⟨j, hj, hw2, k, hk, hkr, hkj, rfl⟩
  · -- swap
    by_cases hjr : j + 1 < r
    · have hmod : (j + 1) % r = j + 1 := Nat.mod_eq_of_lt hjr
      have hps := fun i => psum_cswap (w := chr r A) hr hj i
      simp only [hmod] at hps
      have hne : ∀ i < r, i ≠ j + 1 → psum (cswap r (chr r A) j) i = psum (chr r A) i := by
        intro i _ hi'
        have := hps i
        split_ifs at this <;> omega
      have h1 := hps (j + 1)
      simp only [lt_add_iff_pos_right, Nat.lt_one_iff, lt_self_iff_false, if_true,
        if_false] at h1
      have hcj := hc j
      have hcj1 := hc (j + 1)
      split_ifs at hcj hcj1 with c1 c2 c2
      · exact (case0 (fun i hi => by
          by_cases hi' : i = j + 1
          · subst hi'; omega
          · exact hne i hi hi')).elim
      · -- w_j = a+1, w_{j+1} = a : Type II at j+1
        right
        exact typeII (j + 1) hjr (fun h => by have := hsmall h; omega) hne (by omega)
      · left
        exact typeI (j + 1) hjr (fun _ => c2) hne (by omega)
      · exact (case0 (fun i hi => by
          by_cases hi' : i = j + 1
          · subst hi'; omega
          · exact hne i hi hi')).elim
    · have hjr' : j = r - 1 := by omega
      have hmod : (j + 1) % r = 0 := by rw [show j + 1 = r by omega, Nat.mod_self]
      have hps := fun i => psum_cswap (w := chr r A) hr hj i
      simp only [hmod] at hps
      have hl := chr_last hr hcop
      have h0 := chr_zero (A := A) hr0
      rw [← hjr'] at hl
      exact (caseWp (fun i hi hi' => by
        have := hps i
        split_ifs at this <;> omega)).elim
  · -- slide
    have hw1 : 1 ≤ chr r A j := by omega
    have hps := fun i => psum_slide (w := chr r A) hw1 hkj i
    have hcases : (j + 1 < r ∧ k = j + 1) ∨ (k + 1 = j) ∨ (j = r - 1 ∧ k = 0) ∨
        (j = 0 ∧ k = r - 1) := by
      by_cases hjr : j + 1 < r
      · rw [Nat.mod_eq_of_lt hjr] at hk
        rcases hk with hk | hk
        · exact Or.inl ⟨hjr, hk⟩
        · by_cases hkr' : k + 1 < r
          · rw [Nat.mod_eq_of_lt hkr'] at hk; exact Or.inr (Or.inl hk)
          · rw [show k + 1 = r by omega, Nat.mod_self] at hk
            exact Or.inr (Or.inr (Or.inr ⟨hk.symm, by omega⟩))
      · rw [show j + 1 = r by omega, Nat.mod_self] at hk
        rcases hk with hk | hk
        · exact Or.inr (Or.inr (Or.inl ⟨by omega, hk⟩))
        · by_cases hkr' : k + 1 < r
          · rw [Nat.mod_eq_of_lt hkr'] at hk; exact Or.inr (Or.inl hk)
          · rw [show k + 1 = r by omega, Nat.mod_self] at hk; omega
    rcases hcases with ⟨hjr, rfl⟩ | rfl | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · -- rightward slide: Type II at j+1
      right
      refine typeII (j + 1) hjr (fun h => ?_) (fun i _ hi' => by
        have := hps i; split_ifs at this <;> omega) (by
        have := hps (j + 1); split_ifs at this <;> omega)
      have hs := hsmall h
      have hcj := hc j
      have hms := mod_succ (A := A) hr0 j
      have := Nat.mod_lt (j * A) hr0
      split_ifs at hcj hms with c1
      · omega
      · omega
    · -- leftward slide: Type I at k+1
      left
      refine typeI (k + 1) hj (fun h => ?_) (fun i _ hi' => by
        have := hps i; split_ifs at this <;> omega) (by
        have := hps (k + 1); split_ifs at this <;> omega)
      have hs := hsmall h
      have hcj := hc (k + 1)
      split_ifs at hcj with c1
      · exact c1
      · omega
    · -- right wrap
      exact (caseWp (fun i hi hi' => by
        have := hps i; split_ifs at this <;> omega)).elim
    · -- left wrap: Type I with p = r - 1, needs A ≥ 2r
      left
      have hx := hGu.mul_right_eq_zero.mp (caseWm (fun i hi hi' => by
        have := hps i; split_ifs at this <;> omega))
      refine ⟨r - 1, by omega, by omega, fun h => ?_, ?_⟩
      · have hs := hsmall h
        have := chr_zero (A := A) hr0
        omega
      · rw [show r - 1 + 1 = r by omega]; exact hx

end CollatzSearch.NormReduce

#print axioms CollatzSearch.NormReduce.exists_g
#print axioms CollatzSearch.NormReduce.g_unique
#print axioms CollatzSearch.NormReduce.knight_identity
#print axioms CollatzSearch.NormReduce.knight
#print axioms CollatzSearch.NormReduce.reduce

