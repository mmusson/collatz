import NormMain
import NormGoalAll

/-!
# the one-move Christoffel theorem for ALL `(r, A)` (MAIN GOAL)

* `Sg U V t = Σ_{s<t} U^s V^{t-1-s}` (`Sg_mul_sub`: `Sg·(U-V) = U^t - V^t`; odd, coprime to 3,
  `> 1` for `t ≥ 2`), and `Bf_rep`: the numerator of a `t`-fold repeated block is
  `Sg (2^P) (3^n) t` times the numerator of the block.
* `one_move_not_dvd` (monomial lemma): if every entry of `w` is `c` or `c+1`, `v` is one move from
  `w` and differs from it, and `m > 1` coprime to `6` divides `B(w)`, then `m ∤ B(v)`: each move
  changes `B` by a monomial `±3^a 2^b` (one partial sum moves by `±1`) or doubles all terms but the
  first (wrap moves: `B(v) + 3^{r-1} = 2B(w)` or `2B(v) = B(w) + 3^{r-1}`).
* `no_cycle_one_move_christoffel_all` — the MAIN GOAL (`NormGoal.no_cycle_one_move_christoffel_all`):
  coprime case is `NormMain.main` (`NormMain`); for `d = gcd(A, r) ≥ 2` the cofactor
  `S_d = Sg (2^{A/d}) (3^{r/d}) d` (Solomon 2026, Zenodo 22220730, Prop. 6.3) divides both
  `2^A - 3^r` and `B(chr r A)`, and the monomial lemma applies.
* `knight_all`: `(2^A - 3^r) ∣ B(chr r A) ↔ A = 2r` (Knight 2026 for coprime `(r, A)`; the
  non-coprime extension uses `2^a = 3^b + 1 ⇒ (a,b) = (2,1)`), and
  `one_move_classification`: on `chr r A` and its one-move neighbourhood, `q ∣ B(v)` iff `A = 2r`
  and `v = chr r A` (the trivial cycle).

Prior art: Knight (Christoffel case), Lebel, Mghirbi, Solomon (see
experiments/NORM_CRITERION.md). No rotation identity is needed for wrap moves.
-/

namespace CollatzSearch.NormAll
open CollatzSearch.NormGoal CollatzSearch.NormReduce Finset

/-- `Sg U V t = Σ_{s<t} U^s V^{t-1-s}` (by recursion `Sg (t+1) = V^t + U·Sg t`). -/
def Sg (U V : ℕ) : ℕ → ℕ
  | 0 => 0
  | t + 1 => V ^ t + U * Sg U V t

/-- Numerator `Σ_{j<N} 3^{N-1-j} 2^{f j}` of a word with partial sums `f`. -/
def Bf (f : ℕ → ℕ) (N : ℕ) : ℕ := ∑ j ∈ range N, 3 ^ (N - 1 - j) * 2 ^ f j

/-- `Sg U V t · (U - V) = U^t - V^t` in `ℤ`. -/
theorem Sg_mul_sub (U V t : ℕ) : (Sg U V t : ℤ) * (U - V) = (U : ℤ) ^ t - V ^ t := by
  induction t with
  | zero => simp [Sg]
  | succ t ih => push_cast [Sg]; linear_combination (U : ℤ) * ih

/-- `Sg U V (t+1)` is odd when `U` is even and `V` odd. -/
theorem Sg_odd {U V : ℕ} (hU : 2 ∣ U) (hV : V % 2 = 1) (t : ℕ) : Sg U V (t + 1) % 2 = 1 := by
  obtain ⟨u, rfl⟩ := hU
  have : V ^ t % 2 = 1 := by rw [Nat.pow_mod, hV]; simp
  simp only [Sg]
  rw [Nat.add_mod, this, mul_assoc, Nat.mul_mod_right]

/-- `Sg U V (t+1)` is coprime to 3 when `3 ∤ U` and `3 ∣ V`. -/
theorem Sg_cop3 {U V : ℕ} (hU : Nat.Coprime 3 U) (hV : 3 ∣ V) (t : ℕ) :
    Nat.Coprime 3 (Sg U V (t + 1)) := by
  induction t with
  | zero => simp [Sg]
  | succ t ih =>
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three] at *
    intro h
    have h1 : 3 ∣ V ^ (t + 1) := dvd_pow hV (by omega)
    have h2 : 3 ∣ U * Sg U V (t + 1) := (Nat.dvd_add_right h1).mp (by simpa [Sg] using h)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h2 with h | h
    exacts [hU h, ih h]

/-- `Sg U V d > 1` for `d ≥ 2`, `U ≥ 2` even, `V` odd. -/
theorem one_lt_Sg {U V : ℕ} (hU : 2 ≤ U) (hU2 : 2 ∣ U) (hV : V % 2 = 1) {d : ℕ} (hd : 2 ≤ d) :
    1 < Sg U V d := by
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
  have h1 := Sg_odd hU2 hV e
  have : 1 ≤ Sg U V (e + 1) := by omega
  show 1 < V ^ (e + 1) + U * Sg U V (e + 1)
  have := Nat.mul_le_mul hU this
  omega

/-- **Repetition.** If `f (j + n) = f j + P` then `Bf f (t n) = Sg (2^P) (3^n) t · Bf f n`. -/
theorem Bf_rep {f : ℕ → ℕ} {n P : ℕ} (hf : ∀ j, f (j + n) = f j + P) (t : ℕ) :
    Bf f (t * n) = Sg (2 ^ P) (3 ^ n) t * Bf f n := by
  induction t with
  | zero => simp [Bf, Sg]
  | succ t ih =>
    have hsplit : Bf f ((t + 1) * n) = (3 ^ n) ^ t * Bf f n + 2 ^ P * Bf f (t * n) := by
      unfold Bf
      rw [show (t + 1) * n = n + t * n by ring, sum_range_add, mul_sum, mul_sum]
      congr 1
      · apply sum_congr rfl; intro j hj; have := mem_range.mp hj
        rw [show n + t * n - 1 - j = n * t + (n - 1 - j) by rw [Nat.mul_comm n t]; omega,
          pow_add, pow_mul]; ring
      · apply sum_congr rfl; intro x hx; have := mem_range.mp hx
        rw [show n + t * n - 1 - (n + x) = t * n - 1 - x by omega, add_comm n x, hf, pow_add]
        ring
    rw [hsplit, ih]; simp only [Sg]; ring

/-- **Monomial lemma.** If every entry of `w` on `range r` is `c` or `c+1`, `v` is one move from
`w` and differs from it on `range r`, and `m > 1` is coprime to `6` with `m ∣ B(w)`, then `m ∤ B(v)`. -/
theorem one_move_not_dvd {r m c : ℕ} (hr : 2 ≤ r) (hm : 1 < m)
    (h2 : Nat.Coprime 2 m) (h3 : Nat.Coprime 3 m) {w v : ℕ → ℕ}
    (hw : ∀ i < r, w i = c ∨ w i = c + 1) (hv : OneMove r w v)
    (hne : ∃ j < r, v j ≠ w j) (hBw : m ∣ Bnum r w) : ¬ m ∣ Bnum r v := by
  intro hBv'
  have hnt : Nontrivial (ZMod m) := ZMod.nontrivial_iff.mpr (by omega)
  have h2u : IsUnit (2 : ZMod m) := by simpa using (ZMod.unitOfCoprime 2 h2).isUnit
  have h3u : IsUnit (3 : ZMod m) := by simpa using (ZMod.unitOfCoprime 3 h3).isUnit
  have hr0 : 0 < r := by omega
  have hBv : (Bnum r v : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hBv'
  have hBw0 : (Bnum r w : ZMod m) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr hBw
  rw [cast_Bnum] at hBv hBw0
  have hT : ∀ a b : ℕ, (3 : ZMod m) ^ a * 2 ^ b ≠ 0 :=
    fun a b => ((h3u.pow a).mul (h2u.pow b)).ne_zero
  have caseP : ∀ i0, i0 < r → (∀ i < r, i ≠ i0 → psum v i = psum w i) →
      psum v i0 = psum w i0 + 1 → False := by
    intro i0 hi0 hne' heq
    have := sum_perturb1 (s := range r) (mem_range.mpr hi0)
      (fun i => (3 : ZMod m) ^ (r - 1 - i) * 2 ^ psum w i)
      (fun i => (3 : ZMod m) ^ (r - 1 - i) * 2 ^ psum v i)
      (fun i hi hi' => by rw [hne' i (mem_range.mp hi) hi'])
    rw [hBv, hBw0, heq, pow_succ] at this
    exact hT (r - 1 - i0) (psum w i0) (by linear_combination -this)
  have caseM : ∀ i0, i0 < r → (∀ i < r, i ≠ i0 → psum v i = psum w i) →
      psum v i0 + 1 = psum w i0 → False := by
    intro i0 hi0 hne' heq
    have := sum_perturb1 (s := range r) (mem_range.mpr hi0)
      (fun i => (3 : ZMod m) ^ (r - 1 - i) * 2 ^ psum w i)
      (fun i => (3 : ZMod m) ^ (r - 1 - i) * 2 ^ psum v i)
      (fun i hi hi' => by rw [hne' i (mem_range.mp hi) hi'])
    rw [hBv, hBw0, ← heq, pow_succ] at this
    exact hT (r - 1 - i0) (psum v i0) (by linear_combination this)
  have caseWp : (∀ i < r, i ≠ 0 → psum v i = psum w i + 1) → False := by
    intro h
    have := sum_perturbW (s := range r) (mem_range.mpr hr0)
      (fun i => (3 : ZMod m) ^ (r - 1 - i) * 2 ^ psum w i)
      (fun i => (3 : ZMod m) ^ (r - 1 - i) * 2 ^ psum v i)
      (by simp [psum])
      (fun i hi hi' => by rw [h i (mem_range.mp hi) hi', pow_succ]; ring)
    rw [hBv, hBw0] at this
    exact hT (r - 1 - 0) (psum w 0) (by linear_combination this)
  have caseWm : (∀ i < r, i ≠ 0 → psum v i + 1 = psum w i) → False := by
    intro h
    have := sum_perturbW (s := range r) (mem_range.mpr hr0)
      (fun i => (3 : ZMod m) ^ (r - 1 - i) * 2 ^ psum v i)
      (fun i => (3 : ZMod m) ^ (r - 1 - i) * 2 ^ psum w i)
      (by simp [psum])
      (fun i hi hi' => by rw [← h i (mem_range.mp hi) hi', pow_succ]; ring)
    rw [hBv, hBw0] at this
    exact hT (r - 1 - 0) (psum v 0) (by linear_combination this)
  have caseEq : ∀ j, w j = w ((j + 1) % r) → v = cswap r w j → False := by
    intro j hj hvj
    obtain ⟨i, hi, hvi⟩ := hne
    apply hvi
    rw [hvj]
    unfold cswap
    split_ifs with h1 h2
    · rw [h1, hj]
    · rw [h2, hj]
    · rfl
  rcases hv with ⟨j, hj, hvj⟩ | ⟨j, hj, hw2, k, hk, hkr, hkj, rfl⟩
  · -- swap
    by_cases hjr : j + 1 < r
    · have hmod : (j + 1) % r = j + 1 := Nat.mod_eq_of_lt hjr
      have hps := fun i => psum_cswap (w := w) hr hj i
      simp only [hmod] at hps
      rw [← hvj] at hps
      have hne' : ∀ i < r, i ≠ j + 1 → psum v i = psum w i := by
        intro i _ hi'
        have := hps i
        split_ifs at this <;> omega
      have h1 := hps (j + 1)
      simp only [lt_add_iff_pos_right, Nat.lt_one_iff, lt_self_iff_false, ite_true,
        ite_false] at h1
      rcases hw j hj with a | a <;> rcases hw (j + 1) hjr with b | b
      · exact caseEq j (by rw [hmod]; omega) hvj
      · exact caseP (j + 1) hjr hne' (by omega)
      · exact caseM (j + 1) hjr hne' (by omega)
      · exact caseEq j (by rw [hmod]; omega) hvj
    · have hjr' : j = r - 1 := by omega
      have hmod : (j + 1) % r = 0 := by rw [show j + 1 = r by omega, Nat.mod_self]
      have hps := fun i => psum_cswap (w := w) hr hj i
      simp only [hmod] at hps
      rw [← hvj] at hps
      rcases hw j hj with a | a <;> rcases hw 0 hr0 with b | b
      · exact caseEq j (by rw [hmod]; omega) hvj
      · exact caseWm (fun i hi hi' => by have := hps i; split_ifs at this <;> omega)
      · exact caseWp (fun i hi hi' => by have := hps i; split_ifs at this <;> omega)
      · exact caseEq j (by rw [hmod]; omega) hvj
  · -- slide
    have hw1 : 1 ≤ w j := by omega
    have hps := fun i => psum_slide (w := w) hw1 hkj i
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
    · exact caseM (j + 1) hjr (fun i _ hi' => by
        have := hps i; split_ifs at this <;> omega) (by
        have := hps (j + 1); split_ifs at this <;> omega)
    · exact caseP (k + 1) hj (fun i _ hi' => by
        have := hps i; split_ifs at this <;> omega) (by
        have := hps (k + 1); split_ifs at this <;> omega)
    · exact caseWp (fun i hi hi' => by
        have := hps i; split_ifs at this <;> omega)
    · exact caseWm (fun i hi hi' => by
        have := hps i; split_ifs at this <;> omega)

/-- `chr (dr') (dA')` is the `d`-fold repetition of `chr r' A'`: `B = Sg (2^A') (3^r') d · B(block)`. -/
theorem chr_rep {d r' A' : ℕ} (hd : 0 < d) (hr' : 0 < r') :
    Bnum (d * r') (chr (d * r') (d * A')) = Sg (2 ^ A') (3 ^ r') d * Bnum r' (chr r' A') := by
  have hf : ∀ j, j * (d * A') / (d * r') = j * A' / r' := fun j => by
    rw [show j * (d * A') = d * (j * A') by ring]; exact Nat.mul_div_mul_left _ _ hd
  have e1 : Bnum (d * r') (chr (d * r') (d * A')) = Bf (fun j => j * A' / r') (d * r') := by
    unfold Bnum Bf; apply sum_congr rfl; intro j _; rw [psum_chr, hf]
  have e2 : Bnum r' (chr r' A') = Bf (fun j => j * A' / r') r' := by
    unfold Bnum Bf; apply sum_congr rfl; intro j _; rw [psum_chr]
  rw [e1, e2]
  exact Bf_rep (fun j => by rw [add_mul, mul_comm r' A', Nat.add_mul_div_right _ _ hr']) d

/-- `2^{dA'} - 3^{dr'} = Sg (2^A') (3^r') d · (2^{A'} - 3^{r'})` in `ℤ`. -/
theorem q_rep {d r' A' : ℕ} (hle : 3 ^ (d * r') ≤ 2 ^ (d * A')) :
    ((2 ^ (d * A') - 3 ^ (d * r') : ℕ) : ℤ) =
      (Sg (2 ^ A') (3 ^ r') d : ℤ) * ((2 : ℤ) ^ A' - 3 ^ r') := by
  have := Sg_mul_sub (2 ^ A') (3 ^ r') d
  push_cast at this
  rw [this, Nat.cast_sub hle]
  push_cast
  rw [← pow_mul, ← pow_mul, mul_comm A' d, mul_comm r' d]

/-- Solomon's cofactor: for `d ≥ 2`, `S = Sg (2^A') (3^r') d` is `> 1`, coprime to `6`, and divides
both `2^(dA') - 3^(dr')` and `B(chr (dr') (dA'))`. -/
theorem solomon_factor {d r' A' : ℕ} (hd : 2 ≤ d) (hr' : 0 < r')
    (hq : 3 ^ (d * r') + 1 < 2 ^ (d * A')) :
    1 < Sg (2 ^ A') (3 ^ r') d ∧ Nat.Coprime 2 (Sg (2 ^ A') (3 ^ r') d) ∧
      Nat.Coprime 3 (Sg (2 ^ A') (3 ^ r') d) ∧
      Sg (2 ^ A') (3 ^ r') d ∣ 2 ^ (d * A') - 3 ^ (d * r') ∧
      Sg (2 ^ A') (3 ^ r') d ∣ Bnum (d * r') (chr (d * r') (d * A')) := by
  have hA' : A' ≠ 0 := by rintro rfl; simp at hq
  have hU2 : 2 ∣ 2 ^ A' := dvd_pow_self 2 hA'
  have hU : 2 ≤ 2 ^ A' := Nat.le_of_dvd (by positivity) hU2
  have hV : 3 ^ r' % 2 = 1 := by rw [Nat.pow_mod]; simp
  have hodd := Sg_odd hU2 hV (d - 1)
  rw [show d - 1 + 1 = d by omega] at hodd
  have hc3 := Sg_cop3 (U := 2 ^ A') (V := 3 ^ r') (Nat.Coprime.pow_right _ (by norm_num))
    (dvd_pow_self 3 (by omega)) (d - 1)
  rw [show d - 1 + 1 = d by omega] at hc3
  refine ⟨one_lt_Sg hU hU2 hV hd, Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hodd), hc3, ?_, ?_⟩
  · exact Int.natCast_dvd_natCast.mp ⟨_, q_rep (by omega)⟩
  · rw [chr_rep (by omega) hr']; exact Dvd.intro _ rfl

/-- Every entry of `chr r A` is `⌊A/r⌋` or `⌊A/r⌋ + 1`. -/
theorem chr_two_letter {r A : ℕ} (hr : 0 < r) :
    ∀ i < r, chr r A i = A / r ∨ chr r A i = A / r + 1 := by
  intro i _
  rw [chr_eq hr]
  split_ifs <;> simp

/-- The non-coprime case, in repetition coordinates `r = d r'`, `A = d A'`. -/
theorem main_rep {d r' A' : ℕ} (hd : 2 ≤ d) (hr' : 0 < r')
    (hq : 3 ^ (d * r') + 1 < 2 ^ (d * A')) (v : ℕ → ℕ)
    (hv : OneMove (d * r') (chr (d * r') (d * A')) v)
    (hne : ∃ j < d * r', v j ≠ chr (d * r') (d * A') j) :
    ¬ (2 ^ (d * A') - 3 ^ (d * r')) ∣ Bnum (d * r') v := by
  intro hdiv
  obtain ⟨hm1, hm2, hm3, hmq, hmB⟩ := solomon_factor hd hr' hq
  have hr2 : 2 ≤ d * r' := by nlinarith
  exact one_move_not_dvd hr2 hm1 hm2 hm3 (chr_two_letter (by omega)) hv hne hmB
    (dvd_trans hmq hdiv)

/-- **MAIN GOAL.** For all `r ≥ 2` and `A` with `3^r + 1 < 2^A` (no coprimality), no
word `v` one cyclic adjacent swap or one slide away from `chr r A`, other than `chr r A` itself,
satisfies `(2^A - 3^r) ∣ B(v)`. Exactly `NormGoal.no_cycle_one_move_christoffel_all`. -/
theorem no_cycle_one_move_christoffel_all (r A : ℕ) (hr : 2 ≤ r)
    (hq : 3 ^ r + 1 < 2 ^ A) (v : ℕ → ℕ) (hv : OneMove r (chr r A) v)
    (hne : ∃ j < r, v j ≠ chr r A j) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  have hr0 : 0 < r := by omega
  have hdpos : 0 < Nat.gcd A r := Nat.gcd_pos_of_pos_right _ hr0
  rcases Nat.lt_or_ge (Nat.gcd A r) 2 with hd1 | hd2
  · exact NormMain.main r A hr (show Nat.gcd A r = 1 by omega) hq v hv
  · obtain ⟨r', hr'⟩ := Nat.gcd_dvd_right A r
    obtain ⟨A', hA'⟩ := Nat.gcd_dvd_left A r
    have hr'0 : 0 < r' := by
      rcases Nat.eq_zero_or_pos r' with h | h
      · rw [h, mul_zero] at hr'; omega
      · exact h
    have key := @main_rep (Nat.gcd A r) r' A' hd2 hr'0
    rw [← hr', ← hA'] at key
    exact key hq v hv hne

/-- Sanity check: the statement is literally the `NormGoalAll` statement. -/
example : type_of% @no_cycle_one_move_christoffel_all =
    type_of% @CollatzSearch.NormGoal.no_cycle_one_move_christoffel_all := rfl

/-- `3^b mod 8 ∈ {1, 3}`. -/
theorem three_pow_mod_eight (b : ℕ) : 3 ^ b % 8 = 1 ∨ 3 ^ b % 8 = 3 := by
  induction b with
  | zero => simp
  | succ b ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> norm_num

/-- `2^a = 3^b + 1` with `b ≥ 1` forces `(a, b) = (2, 1)` (reduce mod 8). -/
theorem pow_two_eq_three_pow_succ {a b : ℕ} (hb : 1 ≤ b) (h : 2 ^ a = 3 ^ b + 1) :
    a = 2 ∧ b = 1 := by
  have h8 := three_pow_mod_eight b
  have ha : a < 3 := by
    by_contra ha
    have : 8 ∣ 2 ^ a := by
      have := pow_dvd_pow 2 (show 3 ≤ a by omega); simpa using this
    omega
  have h3 : 3 ^ 1 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) hb
  have hb1 : b = 1 := by
    by_contra hb1
    have : 3 ^ 2 ≤ 3 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
    interval_cases a <;> simp at h <;> omega
  subst hb1
  refine ⟨?_, rfl⟩
  interval_cases a <;> simp at h ⊢

/-- Knight in repetition coordinates: if `q ∣ B(chr)` with `gcd(A', r') = 1`, `d ≥ 1`,
then `A' = 2`, `r' = 1`. -/
theorem knight_rep {d r' A' : ℕ} (hd : 0 < d) (hr' : 0 < r') (hcop : Nat.Coprime A' r')
    (hq : 3 ^ (d * r') + 1 < 2 ^ (d * A'))
    (hdiv : (2 ^ (d * A') - 3 ^ (d * r')) ∣ Bnum (d * r') (chr (d * r') (d * A'))) :
    A' = 2 ∧ r' = 1 := by
  set m := Sg (2 ^ A') (3 ^ r') d with hm
  have hqz := q_rep (d := d) (r' := r') (A' := A') (by omega)
  rw [← hm] at hqz
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with h | h
    · rw [h] at hqz; simp at hqz; omega
    · exact h
  have hVU : 3 ^ r' < 2 ^ A' := by
    by_contra hc
    have : ((2 : ℤ) ^ A' - 3 ^ r') ≤ 0 := by
      have : ((2 ^ A' : ℕ) : ℤ) ≤ ((3 ^ r' : ℕ) : ℤ) := by exact_mod_cast (not_lt.mp hc)
      push_cast at this; linarith
    have : (m : ℤ) * ((2 : ℤ) ^ A' - 3 ^ r') ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos (by positivity) this
    have : (0 : ℤ) < ((2 ^ (d * A') - 3 ^ (d * r') : ℕ) : ℤ) := by exact_mod_cast (by omega)
    linarith
  have hqn : 2 ^ (d * A') - 3 ^ (d * r') = m * (2 ^ A' - 3 ^ r') := by
    have : ((2 ^ (d * A') - 3 ^ (d * r') : ℕ) : ℤ) = ((m * (2 ^ A' - 3 ^ r') : ℕ) : ℤ) := by
      rw [hqz]; push_cast [Nat.cast_sub hVU.le]; ring
    exact_mod_cast this
  rw [hqn, chr_rep hd hr', ← hm] at hdiv
  have h0 := Nat.dvd_of_mul_dvd_mul_left hmpos hdiv
  by_cases hq' : 3 ^ r' + 1 < 2 ^ A'
  · rcases Nat.lt_or_ge r' 2 with h1 | h2
    · have hr1 : r' = 1 := by omega
      subst hr1
      have : Bnum 1 (chr 1 A') = 1 := by simp [Bnum, psum]
      rw [this] at h0
      have := Nat.le_of_dvd one_pos h0
      omega
    · exact absurd h0 (knight h2 hcop hq')
  · have heq : 2 ^ A' = 3 ^ r' + 1 := by omega
    exact pow_two_eq_three_pow_succ hr' heq

/-- **Knight for all `(r, A)`.** For `r ≥ 2` and `3^r + 1 < 2^A`:
`(2^A - 3^r) ∣ B(chr r A) ↔ A = 2r`. -/
theorem knight_all (r A : ℕ) (hr : 2 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) :
    (2 ^ A - 3 ^ r) ∣ Bnum r (chr r A) ↔ A = 2 * r := by
  have hr0 : 0 < r := by omega
  constructor
  · intro hdiv
    have hdpos : 0 < Nat.gcd A r := Nat.gcd_pos_of_pos_right _ hr0
    obtain ⟨r', hr'⟩ := Nat.gcd_dvd_right A r
    obtain ⟨A', hA'⟩ := Nat.gcd_dvd_left A r
    have hr'0 : 0 < r' := by
      rcases Nat.eq_zero_or_pos r' with h | h
      · rw [h, mul_zero] at hr'; omega
      · exact h
    have hcop : Nat.Coprime A' r' := by
      have := Nat.coprime_div_gcd_div_gcd (m := A) (n := r) hdpos
      have e1 : A / Nat.gcd A r = A' := by
        nth_rewrite 1 [hA']; exact Nat.mul_div_cancel_left _ hdpos
      have e2 : r / Nat.gcd A r = r' := by
        nth_rewrite 1 [hr']; exact Nat.mul_div_cancel_left _ hdpos
      rwa [e1, e2] at this
    have key := @knight_rep (Nat.gcd A r) r' A' hdpos hr'0 hcop
    rw [← hr', ← hA'] at key
    obtain ⟨h1, h2⟩ := key hq hdiv
    rw [h1] at hA'; rw [h2] at hr'; omega
  · rintro rfl
    have key := chr_rep (d := r) (r' := 1) (A' := 2) hr0 one_pos
    have hqz := q_rep (d := r) (r' := 1) (A' := 2) (by rw [mul_one, mul_comm]; omega)
    rw [mul_one, mul_comm r 2] at key hqz
    have hB1 : Bnum 1 (chr 1 2) = 1 := by simp [Bnum, psum]
    rw [key, hB1, mul_one]
    have : 2 ^ (2 * r) - 3 ^ r = Sg (2 ^ 2) (3 ^ 1) r := by
      have : ((2 ^ (2 * r) - 3 ^ r : ℕ) : ℤ) = (Sg (2 ^ 2) (3 ^ 1) r : ℤ) := by
        rw [hqz]; norm_num
      exact_mod_cast this
    rw [this]

/-- `Bnum r` depends only on the word on `range r`. -/
theorem Bnum_congr {r : ℕ} {v w : ℕ → ℕ} (h : ∀ j < r, v j = w j) : Bnum r v = Bnum r w := by
  unfold Bnum
  apply sum_congr rfl
  intro i hi
  have : psum v i = psum w i := by
    unfold psum
    exact sum_congr rfl (fun l hl => h l (by have := mem_range.mp hl; have := mem_range.mp hi; omega))
  rw [this]

/-- **Classification of the one-move neighbourhood of `chr r A`, all `(r, A)`.** For `r ≥ 2`,
`3^r + 1 < 2^A`, and `v` equal to `chr r A` (on `range r`) or one move from it:
`q ∣ B(v)` iff `A = 2r` and `v = chr r A` on `range r` (the trivial cycle). -/
theorem one_move_classification (r A : ℕ) (hr : 2 ≤ r) (hq : 3 ^ r + 1 < 2 ^ A) (v : ℕ → ℕ)
    (hv : OneMove r (chr r A) v ∨ ∀ j < r, v j = chr r A j) :
    (2 ^ A - 3 ^ r) ∣ Bnum r v ↔ A = 2 * r ∧ ∀ j < r, v j = chr r A j := by
  by_cases hagree : ∀ j < r, v j = chr r A j
  · rw [Bnum_congr hagree, knight_all r A hr hq]
    exact ⟨fun h => ⟨h, hagree⟩, fun h => h.1⟩
  · push Not at hagree
    have hmove : OneMove r (chr r A) v := by
      rcases hv with h | h
      · exact h
      · obtain ⟨j, hj, hne⟩ := hagree; exact absurd (h j hj) hne
    constructor
    · intro hdiv; exact absurd hdiv (no_cycle_one_move_christoffel_all r A hr hq v hmove hagree)
    · rintro ⟨_, h⟩; obtain ⟨j, hj, hne⟩ := hagree; exact absurd (h j hj) hne

end CollatzSearch.NormAll

#print axioms CollatzSearch.NormAll.Bf_rep
#print axioms CollatzSearch.NormAll.one_move_not_dvd
#print axioms CollatzSearch.NormAll.solomon_factor
#print axioms CollatzSearch.NormAll.no_cycle_one_move_christoffel_all
#print axioms CollatzSearch.NormAll.pow_two_eq_three_pow_succ
#print axioms CollatzSearch.NormAll.knight_all
#print axioms CollatzSearch.NormAll.one_move_classification
