import NormReduce
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# the rotation-numerator shift lift (any gcd) and one unit slid any distance

Notation: `v` a valuation word (letters `≥ 1` below `r`, `psum v r = A`), `3^r + 1 < 2^A`,
`q = 2^A - 3^r`, `c_i = ⌊iA/r⌋`, `Pe` the partial sums of the periodic extension
(`Pe (i + r) = Pe i + A`), `ε_ρ = psum v ρ - c_ρ` the deviation from the Christoffel word.

**Engine (T1, `shift_lift`).** If `q ∣ B(v)` then `q` divides every rotation numerator
`G a = Σ_{j<r} 3^{r-1-j} 2^{Pe(a+j)}` (`G (a+1) = 3 G a + 2^{Pe a} q`), and `G a = 2^{Pe a}·odd`.
For a shift `σ < r` with `σA = rm + t`, `1 ≤ t < r`, the exact identity
`2^H G a - 2^{H+m} G (a-σ) = Σ_{j<r} 3^{r-1-j} 2^{c_{a+j}} κ_{a+j}`,
`κ_i = 2^{H+ε_i} - 2^{H+ε_{i-σ}-w_i}`, `w_i = [iA mod r < t]` (the `t` *special* indices)
holds termwise. If `κ` vanishes on a cyclic window of length `g`, start `a` at the first support
point after it: the right side is `2^{c_a} 3^{g} N` with `|N| < q` (size hypothesis), so `N = 0`,
and the 2-adic valuations force `κ_a = 0`, a contradiction. The support is never empty: otherwise
`Pe (i + σ) = Pe i + m` for all `i`, so `rm = Pe(rσ) = σA = rm + t`.

Prior art: for `σ = A^{-1} mod r` (`t = 1`) and `gcd(A, r) = 1` this is Mghirbi's
rotation-numerator lift (Mghirbi, Zenodo 21734655, Thm 6.3, Thm 6.4 (2-adic nonvanishing via odd
rotation numerators), Lemma 7.2 (maximal cyclic gap)), which works through `ξ ∈ ℤ/q` and needs
coprimality. New here: no `ξ` (we only use `q ∣ G a`), arbitrary `t ≥ 1` (several specials),
any `gcd(A, r)`, and a free window obtained from *arcs* (runs) rather than from a point count.

**Slides (T2/T3 cores).** For `v = slide (chr r A) a b` the deviation is `ε = [b<ρ] - [a<ρ]`
(`∓1` on one arc), so the non-special support of `κ` lies in two cyclic arcs of length
`min(σ, r - σ)` (`slide_cover_a/b`). `free_window` (arc version of `NormArc.free_gap`) gives a free
window of length `g` when `2(ℓ + g - 1) + |E| g < r`.
* `slide_word_coprime`: `gcd = 1`: `σ = A^{-1}` (`t = 1`, special `{0}`) if
  `20 min(σ, r-σ) ≤ 7r`, else `σ = 2A^{-1}` (`t = 2`, specials `{0, A^{-1}}`); `g = ⌊r/10⌋`.
* `slide_word_gcd`: `gcd = d ≥ 2`, `r' = r/d ≥ 2`: `σ ≡ (A/d)^{-1} (mod r')` with
  `min(σ, r-σ) ≤ r'/2`, `t = d`, specials `{0, r', …, (d-1)r'}`, `g = ⌊(r-r')/(d+2)⌋`.
* `few_levels_coprime` (T5): any coprime word with `|ε| ≤ H₀` whose deviation changes level at
  `J` cyclic positions, under `2^{2H₀+174} r^59 < 3^{⌊r/(6J+3)⌋+1}` (Dirichlet: `t ≤ 2J+1`,
  `(2J+1)·min(σ, r-σ) < r`; `J` arcs plus `t` specials).
With the gap `2^A ≤ 2^172 r^58 q` (`gap_all59`) the size hypothesis reduces to
`2^176 r^59 < 3^{g+1}` (`size_ok`, `big_r10`). The assembled theorems for actual slides and
actual `T`-cycles are in `NormShiftSlide.lean`.

Honest scope: word-level / cycle-equation exclusions only. NOT a milestone, NOT
`no_nontrivial_cycles`.
-/

namespace CollatzSearch.NormShift
open CollatzSearch.NormGoal CollatzSearch.NormReduce Finset

/-! ### Periodic extension of the partial sums -/

/-- Partial sums of the periodic extension `i ↦ v (i % r)`. -/
def Pe (r : ℕ) (v : ℕ → ℕ) (i : ℕ) : ℕ := psum (fun j => v (j % r)) i

theorem Pe_succ (r : ℕ) (v : ℕ → ℕ) (i : ℕ) : Pe r v (i + 1) = Pe r v i + v (i % r) := by
  unfold Pe psum; rw [sum_range_succ]

theorem Pe_of_le {r : ℕ} (v : ℕ → ℕ) {i : ℕ} (h : i ≤ r) : Pe r v i = psum v i := by
  unfold Pe psum
  apply sum_congr rfl
  intro j hj
  show v (j % r) = v j
  rw [Nat.mod_eq_of_lt (by have := mem_range.mp hj; omega)]

theorem Pe_zero (r : ℕ) (v : ℕ → ℕ) : Pe r v 0 = 0 := by simp [Pe, psum]

theorem Pe_add {r A : ℕ} {v : ℕ → ℕ} (hA : psum v r = A) (i : ℕ) :
    Pe r v (i + r) = Pe r v i + A := by
  induction i with
  | zero => rw [zero_add, Pe_of_le v le_rfl, hA, Pe_zero]; ring
  | succ i ih =>
    rw [show i + 1 + r = (i + r) + 1 by ring, Pe_succ, Pe_succ, ih, Nat.add_mod_right]; ring

theorem Pe_add_mul {r A : ℕ} {v : ℕ → ℕ} (hA : psum v r = A) (i n : ℕ) :
    Pe r v (i + r * n) = Pe r v i + A * n := by
  induction n with
  | zero => simp
  | succ n ih => rw [mul_add, mul_one, ← add_assoc, Pe_add hA, ih]; ring

theorem Pe_mod {r A : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hA : psum v r = A) (i : ℕ) :
    Pe r v i = psum v (i % r) + A * (i / r) := by
  conv_lhs => rw [← Nat.mod_add_div i r]
  rw [Pe_add_mul hA, Pe_of_le v (Nat.mod_lt _ hr).le]

theorem c_mod {r A : ℕ} (hr : 0 < r) (i : ℕ) : i * A / r = (i % r) * A / r + A * (i / r) := by
  conv_lhs => rw [← Nat.mod_add_div i r]
  rw [add_mul, show r * (i / r) * A = r * (A * (i / r)) by ring, Nat.add_mul_div_left _ _ hr]

theorem Pe_mono {r : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hv1 : ∀ i < r, 1 ≤ v i) (i j : ℕ) :
    Pe r v i + j ≤ Pe r v (i + j) := by
  induction j with
  | zero => simp
  | succ j ih =>
    have := hv1 ((i + j) % r) (Nat.mod_lt _ hr)
    rw [show i + (j + 1) = (i + j) + 1 by ring, Pe_succ]; omega

/-! ### L1: rotation numerators -/

/-- Rotation numerator `G a = Σ_{j<r} 3^{r-1-j} 2^{Pe (a+j)}` (`G 0 = B(v)`). -/
def G (r : ℕ) (v : ℕ → ℕ) (a : ℕ) : ℕ := ∑ j ∈ range r, 3 ^ (r - 1 - j) * 2 ^ Pe r v (a + j)

theorem G_zero {r : ℕ} (v : ℕ → ℕ) : G r v 0 = Bnum r v := by
  unfold G Bnum; apply sum_congr rfl; intro j hj
  rw [zero_add, Pe_of_le v (by have := mem_range.mp hj; omega)]

theorem G_succ {r A : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hA : psum v r = A) (a : ℕ) :
    G r v (a + 1) + 3 ^ r * 2 ^ Pe r v a = 3 * G r v a + 2 ^ A * 2 ^ Pe r v a := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  set S := ∑ j ∈ range n, 3 ^ (n - 1 - j) * 2 ^ Pe (n + 1) v (a + (j + 1)) with hS
  have hG1 : G (n + 1) v (a + 1) = 3 * S + 2 ^ Pe (n + 1) v a * 2 ^ A := by
    unfold G; rw [sum_range_succ, hS, mul_sum]
    congr 1
    · apply sum_congr rfl; intro j hj; have := mem_range.mp hj
      rw [show a + 1 + j = a + (j + 1) by ring, ← mul_assoc, ← pow_succ']
      congr 2; omega
    · rw [show a + 1 + n = a + (n + 1) by ring, Pe_add hA, pow_add]; simp
  have hG2 : G (n + 1) v a = S + 3 ^ n * 2 ^ Pe (n + 1) v a := by
    unfold G; rw [sum_range_succ', hS]
    congr 1
    · apply sum_congr rfl; intro j hj
      rw [show n + 1 - 1 - (j + 1) = n - 1 - j by omega]
  rw [hG1, hG2]; ring

/-- **L1.** `q ∣ B(v)` implies `q` divides every rotation numerator. -/
theorem q_dvd_G {r A : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hA : psum v r = A) (h3 : 3 ^ r ≤ 2 ^ A)
    (hdvd : (2 ^ A - 3 ^ r) ∣ Bnum r v) (a : ℕ) : (2 ^ A - 3 ^ r) ∣ G r v a := by
  induction a with
  | zero => rwa [G_zero]
  | succ a ih =>
    have e := G_succ hr hA a
    have h4 : 3 ^ r * 2 ^ Pe r v a ≤ 2 ^ A * 2 ^ Pe r v a := Nat.mul_le_mul_right _ h3
    have : G r v (a + 1) = 3 * G r v a + (2 ^ A - 3 ^ r) * 2 ^ Pe r v a := by
      rw [Nat.sub_mul]; omega
    rw [this]; exact dvd_add (dvd_mul_of_dvd_right ih _) (dvd_mul_right _ _)

/-- Every rotation numerator is `2^{Pe a}` times an odd number. -/
theorem G_factor {r : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hv1 : ∀ i < r, 1 ≤ v i) (a : ℕ) :
    ∃ u, u % 2 = 1 ∧ G r v a = 2 ^ Pe r v a * u := by
  obtain ⟨n, rfl⟩ : ∃ n, r = n + 1 := ⟨r - 1, by omega⟩
  refine ⟨3 ^ n + 2 * ∑ j ∈ range n,
    3 ^ (n - 1 - j) * 2 ^ (Pe (n + 1) v (a + (j + 1)) - Pe (n + 1) v a - 1), ?_, ?_⟩
  · rw [Nat.add_mul_mod_self_left, Nat.pow_mod]; simp
  · unfold G; rw [sum_range_succ', mul_add, mul_sum, mul_sum, add_comm]
    congr 1
    · simp; ring
    · apply sum_congr rfl; intro j hj
      have := Pe_mono hr hv1 a (j + 1)
      have e : 2 ^ Pe (n + 1) v (a + (j + 1)) = 2 ^ Pe (n + 1) v a *
          (2 * 2 ^ (Pe (n + 1) v (a + (j + 1)) - Pe (n + 1) v a - 1)) := by
        rw [← pow_succ', ← pow_add]; congr 1; omega
      rw [e, show n + 1 - 1 - (j + 1) = n - 1 - j by omega]
      ring

/-! ### L0: the floor shift -/

/-- **L0.** `⌊iA/r⌋ = ⌊(i-σ)A/r⌋ + m + [iA mod r < t]` when `σA = rm + t`, `t < r`. -/
theorem floor_shift {r A σ m t i : ℕ} (hr : 0 < r) (hσ : σ * A = r * m + t) (htr : t < r)
    (hi : σ ≤ i) :
    i * A / r = (i - σ) * A / r + m + (if i * A % r < t then 1 else 0) := by
  have hXY : i * A = (i - σ) * A + r * m + t := by
    rw [add_assoc, ← hσ, ← add_mul, Nat.sub_add_cancel hi]
  have hX := Nat.div_add_mod (i * A) r
  have hY := Nat.div_add_mod ((i - σ) * A) r
  have hXr := Nat.mod_lt (i * A) hr
  have hYr := Nat.mod_lt ((i - σ) * A) hr
  generalize i * A / r = u at *
  generalize (i - σ) * A / r = u' at *
  generalize i * A % r = x at *
  generalize (i - σ) * A % r = y at *
  have hle : u ≤ u' + m + 1 := by
    by_contra hc; push Not at hc
    have : r * (u' + m + 2) ≤ r * u := Nat.mul_le_mul_left _ hc
    rw [mul_add, mul_add] at this; omega
  have hge : u' + m ≤ u := by
    by_contra hc; push Not at hc
    have : r * (u + 1) ≤ r * (u' + m) := Nat.mul_le_mul_left _ hc
    rw [mul_add, mul_add] at this; omega
  rcases (show u = u' + m ∨ u = u' + m + 1 by omega) with h | h
  · subst h; rw [mul_add] at hX
    split_ifs <;> omega
  · subst h; rw [mul_add, mul_add] at hX
    split_ifs <;> omega

/-! ### Residue form of the support -/

/-- Deviation `ε_ρ = psum v ρ - ⌊ρA/r⌋`. -/
def eps (r A : ℕ) (v : ℕ → ℕ) (ρ : ℕ) : ℤ := (psum v ρ : ℤ) - ((ρ * A / r : ℕ) : ℤ)

/-- Special indicator `w_ρ = [ρA mod r < t]`. -/
def wt (r A t ρ : ℕ) : ℤ := if ρ * A % r < t then 1 else 0

/-- `ρ - σ mod r` for `ρ < r`, `σ ≤ r`. -/
def back (r σ ρ : ℕ) : ℕ := if σ ≤ ρ then ρ - σ else ρ + r - σ

/-- `κ_ρ = 0`: `ε_ρ + w_ρ = ε_{ρ-σ}`. -/
def quiet (r A t σ : ℕ) (v : ℕ → ℕ) (ρ : ℕ) : Prop :=
  eps r A v ρ + wt r A t ρ = eps r A v (back r σ ρ)

theorem mod_sub {r σ i : ℕ} (hr : 0 < r) (hσr : σ < r) (hi : σ ≤ i) :
    (i - σ) % r = back r σ (i % r) := by
  have hdm := Nat.mod_add_div i r
  have hlt := Nat.mod_lt i hr
  unfold back
  split_ifs with h
  · have : i - σ = (i % r - σ) + r * (i / r) := by omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]
  · have hn : 1 ≤ i / r := by
      rcases Nat.eq_zero_or_pos (i / r) with h0 | h0
      · rw [h0, mul_zero, add_zero] at hdm; omega
      · exact h0
    have : i - σ = (i % r + r - σ) + r * (i / r - 1) := by
      rw [Nat.mul_sub, mul_one]
      have : r ≤ r * (i / r) := Nat.le_mul_of_pos_right r hn
      omega
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by omega)]

theorem mod_mul_eq (r A i : ℕ) : i * A % r = (i % r) * A % r := by
  exact ((Nat.mod_modEq i r).mul_right A).symm

theorem Z_iff {r A σ m t : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hA : psum v r = A) (hσr : σ < r)
    (hσ : σ * A = r * m + t) (htr : t < r) {i : ℕ} (hi : σ ≤ i) :
    Pe r v i = m + Pe r v (i - σ) ↔ quiet r A t σ v (i % r) := by
  have h1 := Pe_mod hr hA i
  have h2 := Pe_mod hr hA (i - σ)
  have h3 := c_mod (A := A) hr i
  have h4 := c_mod (A := A) hr (i - σ)
  have h5 := floor_shift hr hσ htr hi
  rw [mod_sub hr hσr hi] at h2 h4
  rw [mod_mul_eq r A i] at h5
  unfold quiet eps wt
  split_ifs at h5 ⊢ <;> constructor <;> intro h <;> omega

/-! ### Core of the lift (Mghirbi Thm 6.3/6.4 generalised) -/

theorem abs_pow_sub_le {e f E : ℕ} (he : e ≤ E) (hf : f ≤ E) :
    |(2 : ℤ) ^ e - 2 ^ f| ≤ 2 ^ E := by
  have h1 : (2 : ℤ) ^ e ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) he
  have h2 : (2 : ℤ) ^ f ≤ 2 ^ E := pow_le_pow_right₀ (by norm_num) hf
  have h3 : (0 : ℤ) < 2 ^ e := by positivity
  have h4 : (0 : ℤ) < 2 ^ f := by positivity
  rw [abs_le]; constructor <;> linarith

/-- Term size: `(3^{T-j} 2^{⌊(a+j)A/r⌋ - ⌊aA/r⌋})^r ≤ 2^{AT + r}` for `j ≤ T`. -/
theorem term_pow_le {r A a j T : ℕ} (hr : 0 < r) (h3 : 3 ^ r ≤ 2 ^ A) (hj : j ≤ T) :
    (3 ^ (T - j) * 2 ^ ((a + j) * A / r - a * A / r)) ^ r ≤ 2 ^ (A * T + r) := by
  have hc1 : r * ((a + j) * A / r) ≤ (a + j) * A := Nat.mul_div_le _ _
  have hexp : (a + j) * A = a * A + j * A := add_mul _ _ _
  have hc2 : a * A < r * (a * A / r) + r := by
    have := Nat.div_add_mod (a * A) r; have := Nat.mod_lt (a * A) hr; omega
  have hD : r * ((a + j) * A / r - a * A / r) ≤ j * A + r := by
    rw [Nat.mul_sub]; omega
  rw [mul_pow, ← pow_mul, ← pow_mul]
  calc 3 ^ ((T - j) * r) * 2 ^ (((a + j) * A / r - a * A / r) * r)
      ≤ 2 ^ (A * (T - j)) * 2 ^ (j * A + r) := by
        apply Nat.mul_le_mul
        · rw [mul_comm, pow_mul, pow_mul]; exact Nat.pow_le_pow_left h3 _
        · apply Nat.pow_le_pow_right (by norm_num); rw [mul_comm]; exact hD
    _ = 2 ^ (A * T + r) := by
        rw [← pow_add]; congr 1
        have : A * T = A * (T - j) + A * j := by rw [← mul_add, Nat.sub_add_cancel hj]
        rw [this]; ring

theorem two_adic {a b x y : ℕ} (h : 2 ^ a * x = 2 ^ b * y) (hx : x % 2 = 1)
    (hy : y % 2 = 1) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hab
  · obtain ⟨c, rfl⟩ : ∃ c, b = a + c + 1 := ⟨b - a - 1, by omega⟩
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rw [this] at hx; simp [Nat.mul_mod, pow_succ] at hx
  · exact hab
  · obtain ⟨c, rfl⟩ : ∃ c, a = b + c + 1 := ⟨a - b - 1, by omega⟩
    rw [pow_add, pow_add, mul_assoc, mul_assoc] at h
    have := Nat.eq_of_mul_eq_mul_left (by positivity) h
    rw [← this] at hy; simp [Nat.mul_mod, pow_succ] at hy

/-- **Core of the lift.** `q ∣ B(v)`, `a ≥ σ`, `κ_a ≠ 0` (i.e. `Pe a ≠ m + Pe (a - σ)`),
`κ_{a+j} = 0` for `T < j < r`, all exponents in `[0, E]`, and
`(r 2^E)^r 2^{AT + r} < q^r` give a contradiction. -/
theorem lift_core {r A σ m H E a T : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A) (hdvd : (2 ^ A - 3 ^ r) ∣ Bnum r v)
    (ha : σ ≤ a) (hT : T < r)
    (hval1 : ∀ i, σ ≤ i → i * A / r ≤ H + Pe r v i)
    (hval2 : ∀ i, σ ≤ i → i * A / r ≤ H + m + Pe r v (i - σ))
    (hbd1 : ∀ i, σ ≤ i → H + Pe r v i - i * A / r ≤ E)
    (hbd2 : ∀ i, σ ≤ i → H + m + Pe r v (i - σ) - i * A / r ≤ E)
    (hka : Pe r v a ≠ m + Pe r v (a - σ))
    (hz : ∀ j, T < j → j < r → Pe r v (a + j) = m + Pe r v (a + j - σ))
    (hsz : (r * 2 ^ E) ^ r * 2 ^ (A * T + r) < (2 ^ A - 3 ^ r) ^ r) : False := by
  set q := 2 ^ A - 3 ^ r with hq_def
  have h3 : 3 ^ r ≤ 2 ^ A := by omega
  set c : ℕ → ℕ := fun i => i * A / r with hc_def
  set κ : ℕ → ℤ := fun j => (2 : ℤ) ^ (H + Pe r v (a + j) - c (a + j)) -
    2 ^ (H + m + Pe r v (a + j - σ) - c (a + j)) with hκ_def
  -- exact identity
  have hid : (2 : ℤ) ^ H * (G r v a : ℤ) - 2 ^ (H + m) * (G r v (a - σ) : ℤ) =
      ∑ j ∈ range r, (3 : ℤ) ^ (r - 1 - j) * 2 ^ c (a + j) * κ j := by
    unfold G; push_cast
    rw [mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro j _
    have hv1' := hval1 (a + j) (by omega)
    have hv2' := hval2 (a + j) (by omega)
    have e1 : (2 : ℤ) ^ c (a + j) * 2 ^ (H + Pe r v (a + j) - c (a + j)) =
        2 ^ H * 2 ^ Pe r v (a + j) := by
      rw [← pow_add, ← pow_add]; congr 1; simp only [hc_def]; omega
    have e2 : (2 : ℤ) ^ c (a + j) * 2 ^ (H + m + Pe r v (a + j - σ) - c (a + j)) =
        2 ^ (H + m) * 2 ^ Pe r v (a - σ + j) := by
      rw [← pow_add, ← pow_add, show a - σ + j = a + j - σ by omega]; congr 1
      simp only [hc_def]; omega
    simp only [hκ_def]
    linear_combination (-(3 : ℤ) ^ (r - 1 - j)) * e1 + (3 : ℤ) ^ (r - 1 - j) * e2
  -- window
  set N : ℤ := ∑ j ∈ range (T + 1), (3 : ℤ) ^ (T - j) * 2 ^ (c (a + j) - c a) * κ j with hN
  have hcmono : ∀ j, c a ≤ c (a + j) := by
    intro j; simp only [hc_def]; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
  have hwin : ∑ j ∈ range r, (3 : ℤ) ^ (r - 1 - j) * 2 ^ c (a + j) * κ j =
      2 ^ c a * 3 ^ (r - 1 - T) * N := by
    rw [← sum_subset (range_subset_range.mpr (show T + 1 ≤ r by omega))]
    · rw [hN, mul_sum]; apply sum_congr rfl; intro j hj
      have := mem_range.mp hj
      have := hcmono j
      rw [show (3 : ℤ) ^ (r - 1 - j) = 3 ^ (r - 1 - T) * 3 ^ (T - j) by
          rw [← pow_add]; congr 1; omega,
        show (2 : ℤ) ^ c (a + j) = 2 ^ c a * 2 ^ (c (a + j) - c a) by
          rw [← pow_add]; congr 1; omega]
      ring
    · intro j hj hj'
      have h1 := mem_range.mp hj
      have h2 : T < j := by simp at hj'; omega
      have := hz j h2 h1
      have hk0 : κ j = 0 := by simp only [hκ_def]; rw [this, ← add_assoc, sub_self]
      rw [hk0, mul_zero]
  -- divisibility
  have hqG1 := q_dvd_G hr hA h3 hdvd a
  have hqG2 := q_dvd_G hr hA h3 hdvd (a - σ)
  have hqZ : (q : ℤ) ∣ 2 ^ c a * 3 ^ (r - 1 - T) * N := by
    rw [← hwin, ← hid]
    exact dvd_sub (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hqG1) _)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hqG2) _)
  have hcop : IsCoprime (q : ℤ) ((2 : ℤ) ^ c a * 3 ^ (r - 1 - T)) := by
    have : Nat.Coprime q (2 ^ c a * 3 ^ (r - 1 - T)) :=
      Nat.Coprime.mul_right ((coprime_two hq).symm.pow_right _)
        ((coprime_three hr hq).symm.pow_right _)
    have h' := Nat.isCoprime_iff_coprime.mpr this
    push_cast at h'; exact h'
  have hqN : (q : ℤ) ∣ N := by
    exact hcop.dvd_of_dvd_mul_left hqZ
  -- size
  set x : ℕ → ℕ := fun j => 3 ^ (T - j) * 2 ^ (c (a + j) - c a) with hx
  obtain ⟨jm, hjm, hmax⟩ := exists_max_image (range (T + 1)) x ⟨0, by simp⟩
  have hxr : r * 2 ^ E * x jm < q := by
    have hp := term_pow_le (a := a) hr h3 (mem_range.mp hjm |> Nat.lt_succ_iff.mp)
    apply (Nat.pow_lt_pow_iff_left (show r ≠ 0 by omega)).mp
    calc (r * 2 ^ E * x jm) ^ r = (r * 2 ^ E) ^ r * (x jm) ^ r := by rw [mul_pow]
      _ ≤ (r * 2 ^ E) ^ r * 2 ^ (A * T + r) := Nat.mul_le_mul_left _ hp
      _ < q ^ r := hsz
  have hκb : ∀ j, |κ j| ≤ 2 ^ E := by
    intro j
    exact abs_pow_sub_le (hbd1 (a + j) (by omega)) (hbd2 (a + j) (by omega))
  have hNle : |N| < q := by
    calc |N| ≤ ∑ j ∈ range (T + 1), |(3 : ℤ) ^ (T - j) * 2 ^ (c (a + j) - c a) * κ j| :=
          abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ range (T + 1), ((x jm : ℕ) : ℤ) * 2 ^ E := by
          apply sum_le_sum; intro j hj
          rw [abs_mul]
          have hxj : (3 : ℤ) ^ (T - j) * 2 ^ (c (a + j) - c a) = ((x j : ℕ) : ℤ) := by
            simp only [hx]; push_cast; ring
          rw [hxj, abs_of_nonneg (by positivity)]
          have : ((x j : ℕ) : ℤ) ≤ x jm := by exact_mod_cast hmax j hj
          exact mul_le_mul this (hκb j) (abs_nonneg _) (by positivity)
      _ = ((T + 1 : ℕ) : ℤ) * (x jm * 2 ^ E) := by rw [sum_const, card_range, nsmul_eq_mul]
      _ ≤ ((r * 2 ^ E * x jm : ℕ) : ℤ) := by
          push_cast
          have : ((T + 1 : ℕ) : ℤ) ≤ r := by exact_mod_cast (show T + 1 ≤ r by omega)
          nlinarith [show (0 : ℤ) ≤ x jm * 2 ^ E by positivity]
      _ < q := by exact_mod_cast hxr
  have hN0 : N = 0 := Int.eq_zero_of_abs_lt_dvd hqN hNle
  -- 2-adic conclusion
  have heq : 2 ^ H * G r v a = 2 ^ (H + m) * G r v (a - σ) := by
    have : (2 : ℤ) ^ H * (G r v a : ℤ) - 2 ^ (H + m) * (G r v (a - σ) : ℤ) = 0 := by
      rw [hid, hwin, hN0, mul_zero]
    exact_mod_cast (sub_eq_zero.mp this)
  obtain ⟨u, hu, hGu⟩ := G_factor hr hv1 a
  obtain ⟨u', hu', hGu'⟩ := G_factor hr hv1 (a - σ)
  rw [hGu, hGu', ← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add] at heq
  have := CollatzSearch.NormShift.two_adic heq hu hu'
  omega

/-! ### T1: the shift lift with a free cyclic window -/

/-- `j` (`< r`) lies in the cyclic arc `[s, s + ℓ)` mod `r` (`s ≤ r`). -/
def arc (r s ℓ j : ℕ) : Prop := (s ≤ j ∧ j < s + ℓ) ∨ j + r < s + ℓ

/-- **T1: shift lift, any gcd.** Let `3^r + 1 < 2^A`, `v` with letters `≥ 1`
below `r`, `psum v r = A`; a shift `σ < r` with `σA = rm + t`, `1 ≤ t < r`; heights
`1 - H ≤ ε ≤ E - H`; `g < r` with `(r 2^E)^r 2^{A(r-1-g) + r} < q^r`. If `κ` vanishes on some
cyclic window `[x, x+g)` (`quiet` there), then `q ∤ B(v)`. No coprimality. For `t = 1`,
`gcd = 1` this is Mghirbi's lift (Thm 6.3/6.4, Lemma 7.2). -/
theorem shift_lift {r A σ m t H E g : ℕ} {v : ℕ → ℕ} (hq : 3 ^ r + 1 < 2 ^ A)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A) (hσr : σ < r) (hσ : σ * A = r * m + t)
    (ht : 1 ≤ t) (htr : t < r)
    (hlo : ∀ j < r, j * A / r + 1 ≤ H + psum v j) (hhi : ∀ j < r, H + psum v j ≤ j * A / r + E)
    (hg : g < r) (hsz : (r * 2 ^ E) ^ r * 2 ^ (A * (r - 1 - g) + r) < (2 ^ A - 3 ^ r) ^ r)
    (hrun : ∃ x < r, ∀ j < r, arc r x g j → quiet r A t σ v j) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdvd
  have hr : 0 < r := by omega
  have hlo' : ∀ i, i * A / r + 1 ≤ H + Pe r v i := by
    intro i; have := hlo (i % r) (Nat.mod_lt _ hr); rw [Pe_mod hr hA, c_mod hr]; omega
  have hhi' : ∀ i, H + Pe r v i ≤ i * A / r + E := by
    intro i; have := hhi (i % r) (Nat.mod_lt _ hr); rw [Pe_mod hr hA, c_mod hr]; omega
  have hfl : ∀ i, σ ≤ i → i * A / r ≤ (i - σ) * A / r + m + 1 ∧
      (i - σ) * A / r + m ≤ i * A / r := by
    intro i hi; have := floor_shift hr hσ htr hi; split_ifs at this <;> omega
  have hZ := fun i (hi : σ ≤ i) => Z_iff (v := v) hr hA hσr hσ htr hi
  -- the support is nonempty
  have hne : ∃ ρ < r, ¬ quiet r A t σ v ρ := by
    by_contra hcon; push Not at hcon
    have hall : ∀ i, σ ≤ i → Pe r v i = m + Pe r v (i - σ) :=
      fun i hi => (hZ i hi).mpr (hcon _ (Nat.mod_lt _ hr))
    have hit : ∀ n, Pe r v (n * σ) = n * m := by
      intro n; induction n with
      | zero => simp [Pe_zero]
      | succ n ih =>
        have := hall ((n + 1) * σ) (Nat.le_mul_of_pos_left σ (by omega))
        rw [show (n + 1) * σ - σ = n * σ by rw [add_mul, one_mul, Nat.add_sub_cancel], ih] at this
        rw [this]; ring
    have h1 := hit r
    have h2 := Pe_add_mul hA 0 σ
    rw [zero_add, Pe_zero, zero_add] at h2
    rw [h1, mul_comm A σ, hσ] at h2; omega
  -- the free run, shifted by `r`
  obtain ⟨x, hx, hxrun⟩ := hrun
  have hrun' : ∀ k < g, Pe r v (x + r + k) = m + Pe r v (x + r + k - σ) := by
    intro k hk
    rw [hZ _ (by omega)]
    have hm : (x + r + k) % r = if r ≤ x + k then x + k - r else x + k := by
      rw [show x + r + k = (x + k) + r by ring, Nat.add_mod_right]; exact mod_lt_two (by omega)
    rw [hm]
    apply hxrun
    · split_ifs <;> omega
    · unfold arc; split_ifs <;> omega
  have hper : ∀ i, σ ≤ i → (Pe r v (i + r) = m + Pe r v (i + r - σ) ↔
      Pe r v i = m + Pe r v (i - σ)) := by
    intro i hi; rw [hZ _ (by omega), hZ _ hi, Nat.add_mod_right]
  -- first support point after the run
  have hex : ∃ j, ¬ (Pe r v (x + r + g + j) = m + Pe r v (x + r + g + j - σ)) := by
    obtain ⟨ρ, hρ, hρq⟩ := hne
    refine ⟨ρ + r * ((x + r + g) / r + 1) - (x + r + g), ?_⟩
    have hb := Nat.div_add_mod (x + r + g) r
    have hbl := Nat.mod_lt (x + r + g) hr
    have hge : x + r + g ≤ ρ + r * ((x + r + g) / r + 1) := by rw [mul_add, mul_one]; omega
    rw [Nat.add_sub_cancel' hge, hZ _ (by omega)]
    rwa [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ]
  classical
  have hj0 := Nat.find_spec hex
  have hmin : ∀ j < Nat.find hex, Pe r v (x + r + g + j) = m + Pe r v (x + r + g + j - σ) :=
    fun j hj => by have := Nat.find_min hex hj; push Not at this; exact this
  apply lift_core (σ := σ) (m := m) (H := H) (E := E) (a := x + r + g + Nat.find hex)
    (T := r - 1 - g) hr hq hv1 hA hdvd (by omega) (by omega)
  · intro i _; have := hlo' i; omega
  · intro i hi; have := hlo' (i - σ); have := hfl i hi; omega
  · intro i _; have := hhi' i; omega
  · intro i hi; have := hhi' (i - σ); have := hfl i hi; omega
  · exact hj0
  · intro j hj1 hj2
    have hσ' : σ ≤ x + r + g + Nat.find hex + j - r := by omega
    rw [show x + r + g + Nat.find hex + j = (x + r + g + Nat.find hex + j - r) + r by omega,
      hper _ hσ']
    by_cases hc : Nat.find hex + (j + g - r) < g
    · have := hrun' (Nat.find hex + (j + g - r)) hc
      rw [show x + r + g + Nat.find hex + j - r = x + r + (Nat.find hex + (j + g - r)) by omega]
      exact this
    · have := hmin (Nat.find hex + (j + g - r) - g) (by omega)
      rw [show x + r + g + Nat.find hex + j - r =
        x + r + g + (Nat.find hex + (j + g - r) - g) by omega]
      exact this
  · exact hsz

/-! ### Free cyclic windows (arcs version of `NormArc.free_gap`) -/

/-- Reduce `z < 3r` mod `r`. -/
def red (r z : ℕ) : ℕ := if z < r then z else if z < 2 * r then z - r else z - 2 * r

theorem arc_meet {r s ℓ g x j : ℕ} (hx : x < r) (hj : j < r) (hs : s ≤ r) (hℓ : ℓ ≤ r)
    (hg1 : 1 ≤ g) (hg : g ≤ r) (h1 : arc r x g j) (h2 : arc r s ℓ j) :
    ∃ y < ℓ + g - 1, red r (s + r + 1 + y - g) = x := by
  unfold arc at h1 h2
  refine ⟨(if s ≤ j then j - s else j + r - s) + g - 1 - (if x ≤ j then j - x else j + r - x),
    ?_, ?_⟩
  · split_ifs <;> omega
  · unfold red; split_ifs <;> omega

theorem card_meet {r s ℓ g : ℕ} (hs : s ≤ r) (hℓ : ℓ ≤ r) (hg1 : 1 ≤ g) (hg : g ≤ r)
    (Sx : Finset ℕ) (hSx : ∀ x ∈ Sx, x < r ∧ ∃ j < r, arc r x g j ∧ arc r s ℓ j) :
    Sx.card ≤ ℓ + g - 1 := by
  have hsub : Sx ⊆ (range (ℓ + g - 1)).image (fun y => red r (s + r + 1 + y - g)) := by
    intro x hx
    obtain ⟨hxr, j, hj, h1, h2⟩ := hSx x hx
    obtain ⟨y, hy, hy'⟩ := arc_meet hxr hj hs hℓ hg1 hg h1 h2
    exact mem_image.mpr ⟨y, mem_range.mpr hy, hy'⟩
  calc Sx.card ≤ _ := card_le_card hsub
    _ ≤ (range (ℓ + g - 1)).card := card_image_le
    _ = ℓ + g - 1 := card_range _

/-- **Free window.** Two cyclic arcs of length `ℓ` and a set `E` of points leave a free cyclic
window `[x, x+g)` when `2(ℓ + g - 1) + |E| g < r`. -/
theorem free_window {r g s1 s2 ℓ : ℕ} (E : Finset ℕ) (hs1 : s1 ≤ r) (hs2 : s2 ≤ r) (hℓ : ℓ ≤ r)
    (hE : ∀ e ∈ E, e < r) (hg1 : 1 ≤ g) (hg : g ≤ r)
    (hcount : 2 * (ℓ + g - 1) + E.card * g < r) :
    ∃ x < r, ∀ j < r, arc r x g j → ¬ arc r s1 ℓ j ∧ ¬ arc r s2 ℓ j ∧ j ∉ E := by
  classical
  by_contra hcon
  let bad := fun s l => (range r).filter (fun x => ∃ j < r, arc r x g j ∧ arc r s l j)
  have hbad : ∀ s l, s ≤ r → l ≤ r → (bad s l).card ≤ l + g - 1 := by
    intro s l hs hl
    apply card_meet hs hl hg1 hg
    intro x hx
    simp only [bad, mem_filter, mem_range] at hx
    exact hx
  have hcover : range r ⊆ bad s1 ℓ ∪ bad s2 ℓ ∪ E.biUnion (fun e => bad e 1) := by
    intro x hx
    by_contra hxn
    apply hcon
    refine ⟨x, mem_range.mp hx, fun j hj hxj => ⟨fun h => hxn ?_, fun h => hxn ?_, fun h => hxn ?_⟩⟩
    · exact mem_union_left _ (mem_union_left _ (mem_filter.mpr ⟨hx, j, hj, hxj, h⟩))
    · exact mem_union_left _ (mem_union_right _ (mem_filter.mpr ⟨hx, j, hj, hxj, h⟩))
    · exact mem_union_right _ (mem_biUnion.mpr ⟨j, h, mem_filter.mpr ⟨hx, j, hj, hxj,
        by unfold arc; omega⟩⟩)
  have h1 := card_le_card hcover
  have h2 := card_union_le (bad s1 ℓ ∪ bad s2 ℓ) (E.biUnion (fun e => bad e 1))
  have h3 := card_union_le (bad s1 ℓ) (bad s2 ℓ)
  have h4 : (E.biUnion (fun e => bad e 1)).card ≤ E.card * g := by
    calc _ ≤ ∑ e ∈ E, (bad e 1).card := card_biUnion_le
      _ ≤ ∑ e ∈ E, g := sum_le_sum (fun e he => by
          have := hbad e 1 (hE e he).le (by omega); omega)
      _ = E.card * g := by rw [sum_const, smul_eq_mul]
  have h5 := hbad s1 ℓ hs1 hℓ
  have h6 := hbad s2 ℓ hs2 hℓ
  rw [card_range] at h1
  omega

/-! ### Size bookkeeping -/

/-- From the cycle-equation gap `2^A ≤ 2^172 r^58 q` and `2^{173+E} r^59 < 3^{g+1}`, the size
hypothesis of `shift_lift` holds. -/
theorem size_ok {r A g E : ℕ} (hr : 0 < r) (h3 : 3 ^ r < 2 ^ A) (hg : g < r)
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ (173 + E) * r ^ 59 < 3 ^ (g + 1)) :
    (r * 2 ^ E) ^ r * 2 ^ (A * (r - 1 - g) + r) < (2 ^ A - 3 ^ r) ^ r := by
  set K := 2 ^ 172 * r ^ 58 with hK
  set q := 2 ^ A - 3 ^ r
  have hKpos : 0 < K ^ r := by positivity
  apply Nat.lt_of_mul_lt_mul_right (a := K ^ r)
  calc (r * 2 ^ E) ^ r * 2 ^ (A * (r - 1 - g) + r) * K ^ r
      = (r * 2 ^ E * 2 * K) ^ r * 2 ^ (A * (r - 1 - g)) := by
        rw [pow_add, mul_pow (r * 2 ^ E * 2), mul_pow (r * 2 ^ E)]; ring
    _ = (2 ^ (173 + E) * r ^ 59) ^ r * 2 ^ (A * (r - 1 - g)) := by
        congr 2; rw [hK, pow_add]; ring
    _ < (3 ^ (g + 1)) ^ r * 2 ^ (A * (r - 1 - g)) :=
        Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hbig (by omega)) (by positivity)
    _ = (3 ^ r) ^ (g + 1) * 2 ^ (A * (r - 1 - g)) := by rw [← pow_mul, ← pow_mul, mul_comm (g + 1) r]
    _ ≤ (2 ^ A) ^ (g + 1) * 2 ^ (A * (r - 1 - g)) :=
        Nat.mul_le_mul_right _ (Nat.pow_le_pow_left h3.le _)
    _ = (2 ^ A) ^ r := by
        rw [← pow_mul, ← pow_add, ← pow_mul]; congr 1
        rw [← mul_add]; congr 1; omega
    _ ≤ (K * q) ^ r := Nat.pow_le_pow_left hgap _
    _ = q ^ r * K ^ r := by rw [mul_pow, mul_comm]

set_option exponentiation.threshold 5000 in
/-- `2^176 (10N)^59 < 3^N` for `N ≥ 4091`. -/
theorem big10 : ∀ N, 4091 ≤ N → 2 ^ 176 * (10 * N) ^ 59 < 3 ^ N := by
  intro N hN
  induction N, hN using Nat.le_induction with
  | base => norm_num
  | succ L hL ih =>
    have h1 : (L + 1) * 4091 ≤ 4092 * L := by omega
    have h2 : ((L + 1) * 4091) ^ 59 ≤ (4092 * L) ^ 59 := Nat.pow_le_pow_left h1 59
    have h3 : 4092 ^ 59 ≤ 3 * 4091 ^ 59 := by norm_num
    have h4 : (L + 1) ^ 59 ≤ 3 * L ^ 59 := by
      rw [mul_pow, mul_pow] at h2
      have hp : 0 < 4091 ^ 59 := by positivity
      have : (L + 1) ^ 59 * 4091 ^ 59 ≤ 3 * L ^ 59 * 4091 ^ 59 := by
        calc (L + 1) ^ 59 * 4091 ^ 59 ≤ 4092 ^ 59 * L ^ 59 := h2
          _ ≤ (3 * 4091 ^ 59) * L ^ 59 := Nat.mul_le_mul_right _ h3
          _ = 3 * L ^ 59 * 4091 ^ 59 := by ring
      exact Nat.le_of_mul_le_mul_right this hp
    calc 2 ^ 176 * (10 * (L + 1)) ^ 59 = 10 ^ 59 * (2 ^ 176 * (L + 1) ^ 59) := by ring
      _ ≤ 10 ^ 59 * (2 ^ 176 * (3 * L ^ 59)) := by gcongr
      _ = 3 * (2 ^ 176 * (10 * L) ^ 59) := by ring
      _ < 3 * 3 ^ L := by omega
      _ = 3 ^ (L + 1) := by ring

/-- `2^176 r^59 < 3^{⌊r/10⌋+1}` for `r ≥ 40901`. -/
theorem big_r10 {r : ℕ} (hr : 40901 ≤ r) : 2 ^ 176 * r ^ 59 < 3 ^ (r / 10 + 1) := by
  have h := big10 (r / 10 + 1) (by omega)
  calc 2 ^ 176 * r ^ 59 ≤ 2 ^ 176 * (10 * (r / 10 + 1)) ^ 59 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by omega) _)
    _ < _ := h

/-! ### Slides: the deviation is `∓1` on one arc -/

/-- Indicator of the slide deviation: `ε_ρ = [b < ρ] - [a < ρ]`. -/
def sdev (a b ρ : ℕ) : ℤ := (if b < ρ then 1 else 0) - (if a < ρ then 1 else 0)

/-- Forward change-point cover: if `ε_ρ ≠ ε_{ρ-σ}`, a change point (`min a b + 1` or
`max a b + 1`) lies in `(ρ - σ, ρ]`, i.e. `ρ` lies in one of two arcs of length `σ`. -/
theorem slide_cover_a {r a b σ ρ : ℕ} (_hρ : ρ < r) (_ha : a < r) (_hb : b < r) (_hσr : σ < r)
    (hne : sdev a b ρ ≠ sdev a b (back r σ ρ)) :
    arc r (min a b + 1) σ ρ ∨ arc r (max a b + 1) σ ρ := by
  unfold arc sdev back at *
  split_ifs at * <;> omega

/-- `z ↦ z mod r` for `z < 2r`, with representative in `[0, r]`. -/
def red2 (r z : ℕ) : ℕ := if z ≤ r then z else z - r

/-- Backward change-point cover: arcs of length `r - σ`. -/
theorem slide_cover_b {r a b σ ρ : ℕ} (hρ : ρ < r) (ha : a < r) (hb : b < r) (hσr : σ < r)
    (hne : sdev a b ρ ≠ sdev a b (back r σ ρ)) :
    arc r (red2 r (min a b + 1 + σ)) (r - σ) ρ ∨ arc r (red2 r (max a b + 1 + σ)) (r - σ) ρ := by
  unfold arc sdev back red2 at *
  split_ifs at * <;> omega

/-- **Free run for a slide.** For the slide deviation, specials inside `E` and
`2(min(σ, r-σ) + g - 1) + |E| g < r`, there is a cyclic window of length `g` on which `κ = 0`. -/
theorem slide_run {r A a b σ t g : ℕ} {v : ℕ → ℕ} (E : Finset ℕ) (ha : a < r) (hb : b < r)
    (hσr : σ < r) (heps : ∀ ρ < r, eps r A v ρ = sdev a b ρ)
    (hE : ∀ e ∈ E, e < r) (hspec : ∀ j < r, j * A % r < t → j ∈ E) (hg1 : 1 ≤ g)
    (hcount : 2 * (min σ (r - σ) + g - 1) + E.card * g < r) :
    ∃ x < r, ∀ j < r, arc r x g j → quiet r A t σ v j := by
  have hback : ∀ ρ < r, back r σ ρ < r := by intro ρ hρ; unfold back; split_ifs <;> omega
  have key : ∀ j < r, j ∉ E → ¬ quiet r A t σ v j → sdev a b j ≠ sdev a b (back r σ j) := by
    intro j hj hjE hq heq; apply hq; unfold quiet wt
    rw [ite_eq_right_iff.mpr (fun h => absurd (hspec j hj h) hjE), heps j hj, heps _ (hback j hj), add_zero]
    exact heq
  by_cases hs : σ ≤ r - σ
  · rw [min_eq_left hs] at hcount
    obtain ⟨x, hx, hfree⟩ := free_window (g := g) (s1 := min a b + 1) (s2 := max a b + 1)
      (ℓ := σ) E (by omega) (by omega) (by omega) hE hg1 (by omega) hcount
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    obtain ⟨n1, n2, n3⟩ := hfree j hj hxj
    by_contra hq
    rcases slide_cover_a hj ha hb hσr (key j hj n3 hq) with h | h
    · exact n1 h
    · exact n2 h
  · rw [min_eq_right (by omega)] at hcount
    obtain ⟨x, hx, hfree⟩ := free_window (g := g) (s1 := red2 r (min a b + 1 + σ))
      (s2 := red2 r (max a b + 1 + σ)) (ℓ := r - σ) E (by unfold red2; split_ifs <;> omega)
      (by unfold red2; split_ifs <;> omega) (by omega) hE hg1 (by omega) hcount
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    obtain ⟨n1, n2, n3⟩ := hfree j hj hxj
    by_contra hq
    rcases slide_cover_b hj ha hb hσr (key j hj n3 hq) with h | h
    · exact n1 h
    · exact n2 h

/-- Slide bounds: from `psum v j + [a<j] = ⌊jA/r⌋ + [b<j]` we get `ε = sdev`, and the
height bounds of `shift_lift` with `H = 2`, `E = 3`. -/
theorem slide_bounds {r A a b : ℕ} {v : ℕ → ℕ}
    (hps : ∀ j, psum v j + (if a < j then 1 else 0) = j * A / r + (if b < j then 1 else 0)) :
    (∀ ρ, eps r A v ρ = sdev a b ρ) ∧ (∀ j, j * A / r + 1 ≤ 2 + psum v j) ∧
      (∀ j, 2 + psum v j ≤ j * A / r + 3) := by
  refine ⟨fun ρ => ?_, fun j => ?_, fun j => ?_⟩
  · have := hps ρ; unfold eps sdev; split_ifs at this ⊢ <;> omega
  · have := hps j; split_ifs at this <;> omega
  · have := hps j; split_ifs at this <;> omega

/-- **T2 core (word level, coprime): one unit slid any distance.** Coprime `(A, r)`, `r ≥ 3`,
`3^r + 1 < 2^A`; `v` with letters `≥ 1`, `psum v r = A` and the slide partial sums
`psum v j + [a<j] = ⌊jA/r⌋ + [b<j]`; the gap `2^A ≤ 2^172 r^58 q` and
`2^176 r^59 < 3^{⌊r/10⌋+1}`. Then `q ∤ B(v)`. Shift `σ = A^{-1}` (`t = 1`, one special
point) when `min(σ, r-σ) ≤ 7r/20`, else `σ = 2A^{-1}` (`t = 2`, two special points). -/
theorem slide_word_coprime {r A a b : ℕ} {v : ℕ → ℕ} (hr : 3 ≤ r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (ha : a < r) (hb : b < r) (hv1 : ∀ i < r, 1 ≤ v i)
    (hA : psum v r = A)
    (hps : ∀ j, psum v j + (if a < j then 1 else 0) = j * A / r + (if b < j then 1 else 0))
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ 176 * r ^ 59 < 3 ^ (r / 10 + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  obtain ⟨heps, hlo, hhi⟩ := slide_bounds hps
  obtain ⟨τ, hτr, hτ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hτ' : τ * A % r = 1 := by rw [mul_comm]; exact hτ
  have hinj0 : ∀ j < r, j * A % r = 0 → j = 0 := fun j hj h =>
    mod_inj hcop hj (show 0 < r by omega) (by rw [h]; simp)
  have hinjτ : ∀ j < r, j * A % r = 1 → j = τ := fun j hj h =>
    mod_inj hcop hj hτr (by rw [h, hτ'])
  have hg1 : 1 ≤ r / 10 := by
    by_contra hc
    have : r / 10 = 0 := by omega
    rw [this] at hbig
    have : 1 ≤ r ^ 59 := Nat.one_le_pow _ _ (by omega)
    have : 2 ^ 176 * 1 ≤ 2 ^ 176 * r ^ 59 := Nat.mul_le_mul_left _ this
    norm_num at hbig; omega
  have hsz := size_ok (E := 3) (g := r / 10) (show 0 < r by omega) (by omega) (by omega) hgap
    (by simpa using hbig)
  by_cases hcase : 20 * min τ (r - τ) ≤ 7 * r
  · -- `t = 1`, `σ = τ`
    have hσ : τ * A = r * (τ * A / r) + 1 := by
      have := Nat.div_add_mod (τ * A) r; rw [hτ'] at this; omega
    apply shift_lift (σ := τ) (t := 1) (H := 2) (E := 3) hq hv1 hA hτr hσ le_rfl (by omega)
      (fun j _ => hlo j) (fun j _ => hhi j) (by omega) hsz
    apply slide_run {0} ha hb hτr (fun ρ _ => heps ρ) (by simp; omega)
      (fun j hj h => by simp only [mem_singleton]; exact hinj0 j hj (by omega)) hg1
    rw [card_singleton]; omega
  · -- `t = 2`, `σ = 2τ mod r`
    set σ := 2 * τ % r with hσdef
    have hσr : σ < r := Nat.mod_lt _ (by omega)
    have hσA : σ * A % r = 2 := by
      rw [hσdef, ← mod_mul_eq, mul_assoc, Nat.mul_mod, hτ', mul_one, Nat.mod_mod,
        Nat.mod_eq_of_lt (show 2 < r by omega)]
    have hσ : σ * A = r * (σ * A / r) + 2 := by
      have := Nat.div_add_mod (σ * A) r; rw [hσA] at this; omega
    have hσv : σ = if r ≤ 2 * τ then 2 * τ - r else 2 * τ := mod_lt_two (by omega)
    have hσ0 : σ ≠ 0 := by intro h0; rw [h0] at hσA; simp at hσA
    apply shift_lift (σ := σ) (t := 2) (H := 2) (E := 3) hq hv1 hA hσr hσ (by omega) (by omega)
      (fun j _ => hlo j) (fun j _ => hhi j) (by omega) hsz
    apply slide_run {0, τ} ha hb hσr (fun ρ _ => heps ρ)
      (by intro e he; simp only [mem_insert, mem_singleton] at he; omega)
      (fun j hj h => by
        simp only [mem_insert, mem_singleton]
        rcases (show j * A % r = 0 ∨ j * A % r = 1 by omega) with h0 | h1
        · exact Or.inl (hinj0 j hj h0)
        · exact Or.inr (hinjτ j hj h1)) hg1
    have hc2 : ({0, τ} : Finset ℕ).card * (r / 10) ≤ 2 * (r / 10) :=
      Nat.mul_le_mul_right _ (card_le_two)
    have : 10 * min σ (r - σ) < 3 * r := by
      rw [hσv] at hσ0 ⊢; split_ifs at hσ0 ⊢ <;> omega
    omega

/-- **T3 core (word level, any `d = gcd(A, r) ≥ 2`).** With `r' = r/d ≥ 2`, the shift
`σ ≡ (A/d)^{-1} (mod r')`, `|σ| ≤ r'/2`, has `σA ≡ d (mod r)` and exactly the `d` special
points `0, r', …, (d-1) r'`. Under `2^176 r^59 < 3^{⌊(r - r')/(d+2)⌋+1}` the slide word is
excluded. No coprimality. -/
theorem slide_word_gcd {r A a b d : ℕ} {v : ℕ → ℕ} (hd2 : 2 ≤ d) (hd : Nat.gcd A r = d)
    (hrd : 2 ≤ r / d) (hq : 3 ^ r + 1 < 2 ^ A) (ha : a < r) (hb : b < r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (hps : ∀ j, psum v j + (if a < j then 1 else 0) = j * A / r + (if b < j then 1 else 0))
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ 176 * r ^ 59 < 3 ^ ((r - r / d) / (d + 2) + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  obtain ⟨heps, hlo, hhi⟩ := slide_bounds hps
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h] at hrd; simp at hrd
    · exact h
  set r' := r / d with hr'
  set A' := A / d with hA'
  have hrr : r = d * r' := by rw [hr', Nat.mul_div_cancel' (hd ▸ Nat.gcd_dvd_right A r)]
  have hAA : A = d * A' := by rw [hA', Nat.mul_div_cancel' (hd ▸ Nat.gcd_dvd_left A r)]
  have hcop : Nat.Coprime A' r' := by
    have := Nat.coprime_div_gcd_div_gcd (m := A) (n := r) (by rw [hd]; omega)
    rwa [hd] at this
  obtain ⟨τ, hτr, hτ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have e1 : A' * τ = r' * (A' * τ / r') + 1 := by
    have := Nat.div_add_mod (A' * τ) r'; rw [hτ] at this; omega
  set n := A' * τ / r' with hn
  set k := if 2 * τ ≤ r' then 0 else d - 1 with hk
  set σ := τ + k * r' with hσdef
  have hk1 : k ≤ d - 1 := by rw [hk]; split_ifs <;> omega
  have hkr : k * r' ≤ (d - 1) * r' := Nat.mul_le_mul_right _ hk1
  have hdr : (d - 1) * r' + r' = r := by
    rw [hrr]; conv_rhs => rw [show d = (d - 1) + 1 by omega]
    ring
  have hσr : σ < r := by omega
  have hσ : σ * A = r * (n + k * A') + d := by
    rw [hσdef, hrr, hAA]
    have : d * (A' * τ) = d * (r' * n + 1) := by rw [e1]
    nlinarith [this]
  have hmin : 2 * min σ (r - σ) ≤ r' := by
    rw [hσdef, hk]; split_ifs with h
    · simp only [zero_mul, add_zero]; omega
    · omega
  -- specials
  set E := (range d).image (fun i => i * r') with hE
  have hEr : ∀ e ∈ E, e < r := by
    intro e he; rw [hE, mem_image] at he; obtain ⟨i, hi, rfl⟩ := he
    have := mem_range.mp hi
    have : i * r' + r' ≤ d * r' := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ this
    omega
  have hspec : ∀ j < r, j * A % r < d → j ∈ E := by
    intro j hj hjd
    have h1 : j * A % r = d * (j * A' % r') := by
      rw [hrr, hAA, show j * (d * A') = d * (j * A') by ring, Nat.mul_mod_mul_left]
    have h2 : j * A' % r' = 0 := by
      by_contra hc
      have : d ≤ d * (j * A' % r') := Nat.le_mul_of_pos_right d (by omega)
      omega
    have h3 : r' ∣ j := (Nat.Coprime.symm hcop).dvd_of_dvd_mul_right (Nat.dvd_of_mod_eq_zero h2)
    obtain ⟨c, rfl⟩ := h3
    rw [hE, mem_image]
    refine ⟨c, mem_range.mpr ?_, by ring⟩
    by_contra hc
    have : d * r' ≤ r' * c := by rw [mul_comm r' c]; exact Nat.mul_le_mul_right _ (by omega)
    omega
  have hEc : E.card ≤ d := by rw [hE]; exact card_image_le.trans (by simp)
  -- the window length
  set g := (r - r') / (d + 2) with hg
  have hg1 : 1 ≤ g := by
    by_contra hc
    have : g = 0 := Nat.lt_one_iff.mp (not_le.mp hc)
    rw [this] at hbig
    have : 1 ≤ r ^ 59 := Nat.one_le_pow _ _ hr0
    have : 2 ^ 176 * 1 ≤ 2 ^ 176 * r ^ 59 := Nat.mul_le_mul_left _ this
    norm_num at hbig; omega
  have hgd : (d + 2) * g ≤ r - r' := by rw [hg, mul_comm]; exact Nat.div_mul_le_self _ _
  have hEg : E.card * g ≤ d * g := Nat.mul_le_mul_right _ hEc
  have hdg : (d + 2) * g = d * g + 2 * g := by ring
  have hrr' : r' < r := by
    have : 2 * r' ≤ d * r' := Nat.mul_le_mul_right _ hd2
    omega
  have hsz := size_ok (E := 3) (g := g) hr0 (by omega) (by omega) hgap (by simpa using hbig)
  have hdlt : d < r := by
    have : d * 2 ≤ d * r' := Nat.mul_le_mul_left _ hrd
    omega
  apply shift_lift (σ := σ) (t := d) (H := 2) (E := 3) hq hv1 hA hσr hσ (by omega)
    (by omega) (fun j _ => hlo j) (fun j _ => hhi j) (by omega) hsz
  apply slide_run E ha hb hσr (fun ρ _ => heps ρ) hEr hspec hg1
  clear_value g
  omega

/-! ### T5: few level changes (coprime) -/

/-- Cyclic predecessor on `[0, r)`. -/
def prv (r c : ℕ) : ℕ := if c = 0 then r - 1 else c - 1

/-- **Forward change-point cover.** If `f` changes value (cyclically) only at points of `P`,
and no `c ∈ P` has `ρ ∈ [c, c+σ)`, then `f ρ = f (ρ - σ mod r)`. -/
theorem cover_fwd {r σ ρ : ℕ} (f : ℕ → ℤ) (P : Finset ℕ) (hρ : ρ < r) (hσr : σ < r)
    (hchg : ∀ c < r, f c ≠ f (prv r c) → c ∈ P) (hno : ∀ c ∈ P, ¬ arc r c σ ρ) :
    f ρ = f (back r σ ρ) := by
  have key : ∀ k ≤ σ, f (back r (σ - k) ρ) = f (back r σ ρ) := by
    intro k hk
    induction k with
    | zero => simp
    | succ k ih =>
      rw [← ih (by omega)]
      by_contra hne
      have hc : back r (σ - (k + 1)) ρ < r := by unfold back; split_ifs <;> omega
      have hprev : prv r (back r (σ - (k + 1)) ρ) = back r (σ - k) ρ := by
        unfold prv back; split_ifs <;> omega
      have := hchg _ hc (by rw [hprev]; exact hne)
      exact hno _ this (by unfold arc back; split_ifs <;> omega)
  have := key σ le_rfl
  simpa [back] using this

theorem prv_nx {r ρ k : ℕ} (hρ : ρ < r) (hk : k + 1 ≤ r) :
    prv r (if ρ + (k + 1) < r then ρ + (k + 1) else ρ + (k + 1) - r) =
      (if ρ + k < r then ρ + k else ρ + k - r) := by
  unfold prv
  by_cases h1 : ρ + (k + 1) < r
  · have h2 : ρ + k < r := by omega
    rw [if_pos h1, if_pos h2, if_neg (by omega)]; omega
  · rw [if_neg h1]
    by_cases h2 : ρ + k < r
    · rw [if_pos h2, if_pos (by omega)]; omega
    · rw [if_neg h2, if_neg (by omega)]; omega

/-- **Backward change-point cover.** Same with the arcs `[c + σ - r, c)` of length `r - σ`. -/
theorem cover_bwd {r σ ρ : ℕ} (f : ℕ → ℤ) (P : Finset ℕ) (hρ : ρ < r) (hσr : σ < r)
    (hchg : ∀ c < r, f c ≠ f (prv r c) → c ∈ P)
    (hno : ∀ c ∈ P, ¬ arc r (red2 r (c + σ)) (r - σ) ρ) :
    f ρ = f (back r σ ρ) := by
  have key : ∀ k ≤ r - σ, f (if ρ + k < r then ρ + k else ρ + k - r) = f ρ := by
    intro k hk
    induction k with
    | zero => simp [hρ]
    | succ k ih =>
      rw [← ih (by omega)]
      by_contra hne
      have hc : (if ρ + (k + 1) < r then ρ + (k + 1) else ρ + (k + 1) - r) < r := by
        split_ifs <;> omega
      have hprev : prv r (if ρ + (k + 1) < r then ρ + (k + 1) else ρ + (k + 1) - r) =
          (if ρ + k < r then ρ + k else ρ + k - r) := by
        exact prv_nx hρ (by omega)
      have := hchg _ hc (by rw [hprev]; exact hne)
      exact hno _ this (by unfold arc red2; split_ifs <;> omega)
  have := key (r - σ) le_rfl
  have hb : (if ρ + (r - σ) < r then ρ + (r - σ) else ρ + (r - σ) - r) = back r σ ρ := by
    unfold back; split_ifs <;> omega
  rw [hb] at this; exact this.symm

/-- Free window with arcs from a finset `S` of starts (common length `ℓ`) and points `E`. -/
theorem free_window2 {r g ℓ : ℕ} (S E : Finset ℕ) (hS : ∀ s ∈ S, s ≤ r) (hℓ : ℓ ≤ r)
    (hE : ∀ e ∈ E, e < r) (hg1 : 1 ≤ g) (hg : g ≤ r)
    (hcount : S.card * (ℓ + g - 1) + E.card * g < r) :
    ∃ x < r, ∀ j < r, arc r x g j → (∀ s ∈ S, ¬ arc r s ℓ j) ∧ j ∉ E := by
  classical
  by_contra hcon
  let bad := fun s l => (range r).filter (fun x => ∃ j < r, arc r x g j ∧ arc r s l j)
  have hbad : ∀ s l, s ≤ r → l ≤ r → (bad s l).card ≤ l + g - 1 := by
    intro s l hs hl
    apply card_meet hs hl hg1 hg
    intro x hx
    simp only [bad, mem_filter, mem_range] at hx
    exact hx
  have hcover : range r ⊆ S.biUnion (fun s => bad s ℓ) ∪ E.biUnion (fun e => bad e 1) := by
    intro x hx
    by_contra hxn
    apply hcon
    refine ⟨x, mem_range.mp hx, fun j hj hxj => ⟨fun s hs h => hxn ?_, fun h => hxn ?_⟩⟩
    · exact mem_union_left _ (mem_biUnion.mpr ⟨s, hs, mem_filter.mpr ⟨hx, j, hj, hxj, h⟩⟩)
    · exact mem_union_right _ (mem_biUnion.mpr ⟨j, h, mem_filter.mpr ⟨hx, j, hj, hxj,
        by unfold arc; omega⟩⟩)
  have h1 := card_le_card hcover
  have h2 := card_union_le (S.biUnion (fun s => bad s ℓ)) (E.biUnion (fun e => bad e 1))
  have h3 : (S.biUnion (fun s => bad s ℓ)).card ≤ S.card * (ℓ + g - 1) := by
    calc _ ≤ ∑ s ∈ S, (bad s ℓ).card := card_biUnion_le
      _ ≤ ∑ s ∈ S, (ℓ + g - 1) := sum_le_sum (fun s hs => hbad s ℓ (hS s hs) hℓ)
      _ = S.card * (ℓ + g - 1) := by rw [sum_const, smul_eq_mul]
  have h4 : (E.biUnion (fun e => bad e 1)).card ≤ E.card * g := by
    calc _ ≤ ∑ e ∈ E, (bad e 1).card := card_biUnion_le
      _ ≤ ∑ e ∈ E, g := sum_le_sum (fun e he => by
          have := hbad e 1 (hE e he).le (by omega); omega)
      _ = E.card * g := by rw [sum_const, smul_eq_mul]
  rw [card_range] at h1
  omega

/-- **Dirichlet's approximation (bucket form).** For `K ≥ 1` there is `t ∈ [1, K]` with
`K · min(tτ mod r, r - tτ mod r) < r`. -/
theorem dirichlet {r τ K : ℕ} (hr : 0 < r) (hK : 1 ≤ K) :
    ∃ t, 1 ≤ t ∧ t ≤ K ∧ K * min (t * τ % r) (r - t * τ % r) < r := by
  classical
  have hmaps : ∀ u ∈ range (K + 1), (u * τ % r) * K / r ∈ range K := by
    intro u _
    rw [mem_range]
    apply Nat.div_lt_of_lt_mul
    have := Nat.mod_lt (u * τ) hr
    exact Nat.mul_lt_mul_of_pos_right this (by omega)
  obtain ⟨u1, hu1, u2, hu2, hne, heq⟩ :=
    exists_ne_map_eq_of_card_lt_of_maps_to (by simp) hmaps
  have main : ∀ u1 u2, u1 < u2 → u2 ≤ K → (u1 * τ % r) * K / r = (u2 * τ % r) * K / r →
      ∃ t, 1 ≤ t ∧ t ≤ K ∧ K * min (t * τ % r) (r - t * τ % r) < r := by
    intro u1 u2 h12 hu2 heq
    refine ⟨u2 - u1, by omega, by omega, ?_⟩
    have hy : u2 * τ % r = (u1 * τ % r + (u2 - u1) * τ % r) % r := by
      rw [← Nat.add_mod, ← add_mul, Nat.add_sub_cancel' h12.le]
    have hxr : u1 * τ % r < r := Nat.mod_lt _ hr
    have hσr : (u2 - u1) * τ % r < r := Nat.mod_lt _ hr
    generalize u1 * τ % r = x at *
    generalize (u2 - u1) * τ % r = σ at *
    generalize u2 * τ % r = y at *
    rw [mod_lt_two (show x + σ < 2 * r by omega)] at hy
    have hb1 := Nat.div_add_mod (x * K) r
    have hb2 := Nat.div_add_mod (y * K) r
    have hm1 := Nat.mod_lt (x * K) hr
    have hm2 := Nat.mod_lt (y * K) hr
    rw [heq] at hb1
    have hd1 : x * K < y * K + r := by omega
    have hd2 : y * K < x * K + r := by omega
    split_ifs at hy with hc
    · have : K * min σ (r - σ) ≤ K * (r - σ) := Nat.mul_le_mul_left _ (min_le_right _ _)
      have e : K * (r - σ) + y * K = x * K := by
        rw [hy, mul_comm K, ← add_mul]; congr 1; omega
      omega
    · have : K * min σ (r - σ) ≤ K * σ := Nat.mul_le_mul_left _ (min_le_left _ _)
      have e : y * K = x * K + K * σ := by rw [hy]; ring
      omega
  rcases lt_or_gt_of_ne hne with h | h
  · exact main u1 u2 h (by simp at hu2; omega) heq
  · exact main u2 u1 h (by simp at hu1; omega) heq.symm

/-- **T5: few level changes, coprime.** Let `gcd(A, r) = 1`, `0 < r`,
`3^r + 1 < 2^A`, `v` with letters `≥ 1` below `r`, `psum v r = A`, deviation
`|ε_j| ≤ H₀` (`ε_j = psum v j - ⌊jA/r⌋`), and suppose `ε` changes value (cyclically:
`ε_c ≠ ε_{c-1 mod r}`) only at points of `P`, `J = |P|`. With the gap `2^A ≤ 2^172 r^58 q`
and `2^{2H₀+174} r^59 < 3^{⌊r/(6J+3)⌋+1}`, `q ∤ B(v)`. Proof: Dirichlet gives `t ≤ 2J+1` with
`(2J+1)·min(σ, r-σ) < r`, `σ = tA^{-1} mod r`; the non-special support lies in `J` arcs of length
`min(σ, r-σ)` (change-point covers) plus `t` specials; a free window of length
`g = ⌊r/(6J+3)⌋` follows; `shift_lift` with `H = H₀ + 1`, `E = 2H₀ + 1`.

Relation to prior art: this is a run-count / level-change VARIANT of Mghirbi's support-height
criterion (Zenodo 21734655), not a uniform strengthening. Mghirbi compares
`3^{p/(2s+1)}` with `2^{14.3}(8s+2)^{2H} p^{13.3}` in the number `s` of defect points; ours
compares `3^{r/(6J+3)}` with `2^{2H₀+174} r^59` in the number `J` of level changes (`2s+1` vs
`6J+3`, `p^{13.3}` vs `r^59`). Ours wins for plateau / run-structured deviations (`J ≪ s`) and
loses for isolated defects (`J ≈ 2s`). Single-divisor version: `NormLebel.few_levels_coprime_dvd`. -/
theorem few_levels_coprime {r A H₀ : ℕ} {v : ℕ → ℕ} (hr : 0 < r) (hcop : Nat.Coprime A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, eps r A v c ≠ eps r A v (prv r c) → c ∈ P)
    (hup : ∀ j < r, psum v j ≤ j * A / r + H₀) (hdn : ∀ j < r, j * A / r ≤ psum v j + H₀)
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ (2 * H₀ + 174) * r ^ 59 < 3 ^ (r / (6 * P.card + 3) + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  set J := P.card with hJ
  set g := r / (6 * J + 3) with hg
  have hg1 : 1 ≤ g := by
    by_contra hc
    have : g = 0 := Nat.lt_one_iff.mp (not_le.mp hc)
    rw [this, zero_add, pow_one] at hbig
    have h3 : 3 ≤ 2 ^ (2 * H₀ + 174) * r ^ 59 :=
      calc 3 ≤ 2 ^ (2 * H₀ + 174) :=
            le_trans (by norm_num : 3 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hgK : (6 * J + 3) * g ≤ r := by rw [hg, mul_comm]; exact Nat.div_mul_le_self _ _
  have hgr : g < r := by
    have : 3 * g ≤ (6 * J + 3) * g := Nat.mul_le_mul_right g (by omega)
    omega
  have hJr : 6 * J + 3 ≤ r := by
    have : (6 * J + 3) * 1 ≤ (6 * J + 3) * g := Nat.mul_le_mul_left _ hg1
    omega
  obtain ⟨τ, hτr, hτ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hτ' : τ * A % r = 1 := by rw [mul_comm]; exact hτ
  obtain ⟨t, ht1, htK, hdist⟩ := dirichlet (τ := τ) (K := 2 * J + 1) hr (by omega)
  set σ := t * τ % r with hσdef
  have hσr : σ < r := Nat.mod_lt _ hr
  have htr : t < r := by omega
  have hσA : σ * A % r = t := by
    rw [hσdef, ← mod_mul_eq, mul_assoc, Nat.mul_mod, hτ', mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt htr]
  have hσ : σ * A = r * (σ * A / r) + t := by
    have := Nat.div_add_mod (σ * A) r; rw [hσA] at this; omega
  -- specials
  set E := (range t).image (fun u => u * τ % r) with hE
  have hEr : ∀ e ∈ E, e < r := by
    intro e he; rw [hE, mem_image] at he; obtain ⟨u, _, rfl⟩ := he; exact Nat.mod_lt _ hr
  have hspec : ∀ j < r, j * A % r < t → j ∈ E := by
    intro j hj hjt
    rw [hE, mem_image]
    refine ⟨j * A % r, mem_range.mpr hjt, ?_⟩
    apply mod_inj hcop (Nat.mod_lt _ hr) hj
    rw [← mod_mul_eq, mul_assoc, Nat.mul_mod, hτ', mul_one, Nat.mod_mod, Nat.mod_mod]
  have hEc : E.card ≤ t := card_image_le.trans (by simp)
  -- heights
  have hlo : ∀ j < r, j * A / r + 1 ≤ (H₀ + 1) + psum v j := fun j hj => by
    have := hdn j hj; omega
  have hhi : ∀ j < r, (H₀ + 1) + psum v j ≤ j * A / r + (2 * H₀ + 1) := fun j hj => by
    have := hup j hj; omega
  have hsz := size_ok (E := 2 * H₀ + 1) (g := g) hr (by omega) (by omega) hgap
    (by rw [show 173 + (2 * H₀ + 1) = 2 * H₀ + 174 by ring]; exact hbig)
  apply shift_lift (σ := σ) (t := t) (H := H₀ + 1) (E := 2 * H₀ + 1) hq hv1 hA hσr hσ ht1 htr
    hlo hhi (by omega) hsz
  -- counting
  have hcount : ∀ ℓ, (2 * J + 1) * ℓ < r → ∀ S : Finset ℕ, S.card ≤ J →
      S.card * (ℓ + g - 1) + E.card * g < r := by
    intro ℓ hℓ S hS
    have e1 : 3 * J * ((2 * J + 1) * ℓ + 1) ≤ 3 * J * r := Nat.mul_le_mul_left _ hℓ
    have e2 : (J + t) * ((6 * J + 3) * g) ≤ (J + t) * r := Nat.mul_le_mul_left _ hgK
    have e3 : (J + t) * r ≤ (3 * J + 1) * r := Nat.mul_le_mul_right _ (by omega)
    have key : (6 * J + 3) * (J * ℓ + J * g + t * g) < (6 * J + 3) * r := by nlinarith
    have key' : J * ℓ + J * g + t * g < r := Nat.lt_of_mul_lt_mul_left key
    have f1 : S.card * (ℓ + g - 1) ≤ J * (ℓ + g - 1) := Nat.mul_le_mul_right _ hS
    have f2 : E.card * g ≤ t * g := Nat.mul_le_mul_right _ hEc
    have f3 : J * (ℓ + g - 1) + J = J * ℓ + J * g := by
      rw [← mul_add_one, ← mul_add]; congr 1; omega
    omega
  have hback : ∀ ρ < r, back r σ ρ < r := by intro ρ hρ; unfold back; split_ifs <;> omega
  have hchg' : ∀ c < r, eps r A v c ≠ eps r A v (prv r c) → c ∈ P := hchg
  by_cases hs : σ ≤ r - σ
  · rw [min_eq_left hs] at hdist
    obtain ⟨x, hx, hfree⟩ := free_window2 (g := g) (ℓ := σ) P E (fun s hs => (hP s hs).le)
      (by omega) hEr hg1 (by omega) (hcount σ hdist P le_rfl)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    obtain ⟨n1, n2⟩ := hfree j hj hxj
    unfold quiet wt
    rw [ite_eq_right_iff.mpr (fun h => absurd (hspec j hj h) n2), add_zero]
    exact cover_fwd (eps r A v) P hj hσr hchg' n1
  · rw [min_eq_right (by omega)] at hdist
    set S := P.image (fun c => red2 r (c + σ)) with hS
    obtain ⟨x, hx, hfree⟩ := free_window2 (g := g) (ℓ := r - σ) S E
      (by intro s hs; rw [hS, mem_image] at hs; obtain ⟨c, hc, rfl⟩ := hs
          have := hP c hc; unfold red2; split_ifs <;> omega)
      (by omega) hEr hg1 (by omega) (hcount (r - σ) hdist S card_image_le)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    obtain ⟨n1, n2⟩ := hfree j hj hxj
    unfold quiet wt
    rw [ite_eq_right_iff.mpr (fun h => absurd (hspec j hj h) n2), add_zero]
    exact cover_bwd (eps r A v) P hj hσr hchg'
      (fun c hc => n1 _ (mem_image.mpr ⟨c, hc, rfl⟩))

end CollatzSearch.NormShift

#print axioms CollatzSearch.NormShift.Pe_add
#print axioms CollatzSearch.NormShift.G_succ
#print axioms CollatzSearch.NormShift.q_dvd_G
#print axioms CollatzSearch.NormShift.G_factor
#print axioms CollatzSearch.NormShift.floor_shift
#print axioms CollatzSearch.NormShift.Z_iff
#print axioms CollatzSearch.NormShift.term_pow_le
#print axioms CollatzSearch.NormShift.lift_core
#print axioms CollatzSearch.NormShift.shift_lift
#print axioms CollatzSearch.NormShift.arc_meet
#print axioms CollatzSearch.NormShift.free_window
#print axioms CollatzSearch.NormShift.size_ok
#print axioms CollatzSearch.NormShift.big10
#print axioms CollatzSearch.NormShift.big_r10
#print axioms CollatzSearch.NormShift.slide_cover_a
#print axioms CollatzSearch.NormShift.slide_cover_b
#print axioms CollatzSearch.NormShift.slide_run
#print axioms CollatzSearch.NormShift.slide_bounds
#print axioms CollatzSearch.NormShift.slide_word_coprime
#print axioms CollatzSearch.NormShift.slide_word_gcd
#print axioms CollatzSearch.NormShift.cover_fwd
#print axioms CollatzSearch.NormShift.cover_bwd
#print axioms CollatzSearch.NormShift.free_window2
#print axioms CollatzSearch.NormShift.dirichlet
#print axioms CollatzSearch.NormShift.few_levels_coprime
