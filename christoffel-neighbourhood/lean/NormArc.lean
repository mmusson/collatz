import NormWindow

/-!
# cyclic arcs and few-site perturbations for `gcd(A, r) ≥ 2`

Notation: `d = gcd(A, r) ≥ 2`, `chr r A` the Christoffel word (partial sums `⌊jA/r⌋`),
`B(v) = Σ_{j<r} 3^{r-1-j} 2^{psum v j}` the Böhm–Sontacchi numerator, `q = 2^A - 3^r`,
`S_d` Solomon's cofactor (Solomon 2026, Zenodo 22220730, Prop. 6.3: `S_d ∣ q`, `S_d ∣ B(chr)`,
`gcd(S_d, 6) = 1`, `S_d ≥ 2^{A - A/d}`).

* `seq_inj`: `Σ_{s<w} 3^{w-1-s} 2^{f s}` is injective on strictly increasing `f` (2-adic).
* `window_core`: the `NormCofactor` size argument abstracted to any strictly increasing `α` near `⌊jA/r⌋`.
* **T1** `no_cycle_arc_noncoprime`: the window theorem of `NormWindow` (`NormWindow`) for *cyclic* arcs
  `[k, k+w)` mod `r`. Mod `S_d`, `3^r ≡ 2^A`, so multiplying `Δ = B(v) - B(chr)` by `3^t` folds a
  wrapped arc into a linear window of the extended partial sums `a_{j+r} = a_j + A`.
* **T2** `no_cycle_few_sites_noncoprime`: if `(r 2^{2h+1})^{d-1} < 2^{A/d}`, every word (entries
  `≥ 1`, `psum v r = A`) whose partial sums differ from chr's at between `1` and `d - 1` indices,
  each by at most `h`, has `q ∤ B(v)` (free cyclic gap by double counting + T1).
* Cycle forms `cycle_arc_noncoprime`, `cycle_few_sites_noncoprime`; numerical non-vacuity
  certificates `witness_d3`, `witness_d4` (kernel `decide`).

Scope: word-level statements, `gcd(A, r) ≥ 2` only; For actual cycles the
Christoffel entries are in `{1, 2}` (`L < 2r`), which caps realisable heights; for `d = 3` two
sites are already covered by `NormCofactor.no_cycle_two_site_noncoprime`, so T2 is new for
cycles when `d ≥ 4` (three or more sites), and T1 is new for wrapping arcs with `≥ 3` sites.
Brute force (all words deviating at `≤ K` indices by `≤ h`): `(r,A,K,h) = (12,40,3,1)`: 1562
words, `(12,40,3,2)`: 10596, `(12,20,3,2)`: 609, `(8,20,3,2)`: 1140, `(9,24,2,2)`: 336 —
no `q ∣ B(v)` (beyond the theorem's hypotheses too). Prior art: Knight, Lebel, Mghirbi, Solomon.
-/

namespace Collatz.NormArc
open Collatz.NormGoal Collatz.NormReduce Collatz.NormAll
  Collatz.NormCofactor Collatz.NormWindow Finset

theorem tail_factor (n : ℕ) (F : ℕ → ℕ) (hF : ∀ s < n, F 0 + 1 ≤ F (s + 1)) :
    ∑ s ∈ range (n + 1), 3 ^ (n + 1 - 1 - s) * 2 ^ F s =
      2 ^ F 0 * (3 ^ n + 2 * ∑ s ∈ range n, 3 ^ (n - 1 - s) * 2 ^ (F (s + 1) - F 0 - 1)) := by
  rw [sum_range_succ', mul_add, mul_sum, mul_sum, add_comm]
  congr 1
  · simp; ring
  · apply sum_congr rfl
    intro s hs
    have := hF s (mem_range.mp hs)
    rw [show n + 1 - 1 - (s + 1) = n - 1 - s by omega,
      show 2 ^ F (s + 1) = 2 ^ F 0 * (2 * 2 ^ (F (s + 1) - F 0 - 1)) by
        rw [← pow_succ', ← pow_add]; congr 1; omega]
    ring

theorem mono_ge {n : ℕ} {F : ℕ → ℕ} (hF : ∀ s, s + 1 < n + 1 → F s < F (s + 1)) :
    ∀ s < n, F 0 + 1 ≤ F (s + 1) := by
  intro s hs
  induction s with
  | zero => exact hF 0 (by omega)
  | succ s ihs => have := ihs (by omega); have := hF (s + 1) (by omega); omega

/-- **2-adic injectivity for strictly increasing exponent sequences.** If `f, g` are strictly
increasing on `[0, w)` and `Σ_{s<w} 3^{w-1-s} 2^{f s} = Σ_{s<w} 3^{w-1-s} 2^{g s}`, then
`f = g` on `[0, w)`. -/
theorem seq_inj : ∀ {w : ℕ} {f g : ℕ → ℕ}, (∀ s, s + 1 < w → f s < f (s + 1)) →
    (∀ s, s + 1 < w → g s < g (s + 1)) →
    ∑ s ∈ range w, 3 ^ (w - 1 - s) * 2 ^ f s = ∑ s ∈ range w, 3 ^ (w - 1 - s) * 2 ^ g s →
    ∀ s < w, f s = g s := by
  intro w
  induction w with
  | zero => intro f g _ _ _ s hs; omega
  | succ n ih =>
    intro f g hf hg h
    have hf0 := mono_ge hf
    have hg0 := mono_ge hg
    rw [tail_factor n f hf0, tail_factor n g hg0] at h
    have odd1 : ∀ T : ℕ, (3 ^ n + 2 * T) % 2 = 1 := by
      intro T; rw [Nat.add_mul_mod_self_left, Nat.pow_mod]; simp
    have e0 : f 0 = g 0 := two_adic_cancel h (odd1 _) (odd1 _)
    rw [e0] at h
    have h2 := Nat.eq_of_mul_eq_mul_left (by positivity) h
    have h3 : ∑ s ∈ range n, 3 ^ (n - 1 - s) * 2 ^ (f (s + 1) - f 0 - 1) =
        ∑ s ∈ range n, 3 ^ (n - 1 - s) * 2 ^ (g (s + 1) - g 0 - 1) := by
      rw [← e0]; rw [← e0] at h2; omega
    have hih := ih (f := fun s => f (s + 1) - f 0 - 1) (g := fun s => g (s + 1) - g 0 - 1)
      (by intro s hs; have := hf (s + 1) (by omega); have := hf0 s (by omega); omega)
      (by intro s hs; have := hg (s + 1) (by omega); have := hg0 s (by omega); omega)
      h3
    intro s hs
    rcases s with _ | s
    · exact e0
    · have := hih s (by omega); have := hf0 s (by omega); have := hg0 s (by omega)
      omega

/-- **Size core of the window argument (abstracted).** Let `S` be odd with `2^{A-A'} ≤ S`,
`3^r ≤ 2^A`, `r ≤ A`, and `(w 2^{2h+1})^r 2^{(w-1)A} < 2^{(A-A')r}`. Let `α` be strictly
increasing on `[k, k+w)`, within `h` of `γ j = ⌊jA/r⌋` there, and not equal to `γ` there. Then
`S ∤ Σ_{s<w} 3^{w-1-s}(2^{α(k+s)} - 2^{γ(k+s)})`. -/
theorem window_core {r A A' h k w S : ℕ} (hr0 : 0 < r) (hAr : r ≤ A) (h3r : 3 ^ r ≤ 2 ^ A)
    (hS2 : Nat.Coprime 2 S) (hUS : 2 ^ (A - A') ≤ S)
    (hW : (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * A) < 2 ^ ((A - A') * r))
    (α : ℕ → ℕ) (hmonoα : ∀ s, s + 1 < w → α (k + s) < α (k + s + 1))
    (hup : ∀ s < w, α (k + s) ≤ (k + s) * A / r + h)
    (hdn : ∀ s < w, (k + s) * A / r ≤ α (k + s) + h)
    (hne : ∃ s < w, α (k + s) ≠ (k + s) * A / r)
    (hdvd : (S : ℤ) ∣ ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ α (k + s) - 2 ^ ((k + s) * A / r))) : False := by
  set m := k * A / r - h with hm
  have hmono : ∀ s, k * A / r ≤ (k + s) * A / r := by
    intro s; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
  have hγs : ∀ j, j * A / r + 1 ≤ (j + 1) * A / r := by
    intro j
    have : j * A / r + 1 = (j * A + r) / r := by rw [Nat.add_div_right _ hr0]
    rw [this]; apply Nat.div_le_div_right; rw [add_mul, one_mul]; omega
  set X : ℤ := ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
    ((2 : ℤ) ^ (α (k + s) - m) - 2 ^ ((k + s) * A / r - m)) with hX
  have hTX : ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ α (k + s) - 2 ^ ((k + s) * A / r)) = 2 ^ m * X := by
    rw [hX, mul_sum]
    apply sum_congr rfl
    intro s hs
    have hs' := mem_range.mp hs
    have hma : m ≤ α (k + s) := by have := hdn s hs'; have := hmono s; omega
    have hmc : m ≤ (k + s) * A / r := le_trans (Nat.sub_le _ _) (hmono s)
    have ea : (2 : ℤ) ^ α (k + s) = 2 ^ m * 2 ^ (α (k + s) - m) := by
      rw [← pow_add]; congr 1; omega
    have ec : (2 : ℤ) ^ ((k + s) * A / r) = 2 ^ m * 2 ^ ((k + s) * A / r - m) := by
      rw [← pow_add]; congr 1; omega
    rw [ea, ec]; ring
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hTX
    simp only [mul_sub, sum_sub_distrib, sub_eq_zero] at hTX
    have hN : ∑ s ∈ range w, 3 ^ (w - 1 - s) * 2 ^ α (k + s) =
        ∑ s ∈ range w, 3 ^ (w - 1 - s) * 2 ^ ((k + s) * A / r) := by exact_mod_cast hTX
    obtain ⟨s0, hs0, hne0⟩ := hne
    exact hne0 (seq_inj (f := fun s => α (k + s)) (g := fun s => (k + s) * A / r)
      (fun s hs => hmonoα s hs) (fun s _ => Nat.lt_of_succ_le (hγs (k + s))) hN s0 hs0)
  have hSX : (S : ℤ) ∣ X := by
    rw [hTX] at hdvd
    have c2 : IsCoprime (S : ℤ) 2 := by
      have := Nat.isCoprime_iff_coprime.mpr hS2.symm; simpa using this
    exact (c2.pow_right (n := m)).dvd_of_dvd_mul_left hdvd
  clear_value X m
  have hwpos : 0 < w := by
    rcases Nat.eq_zero_or_pos w with h0 | h0
    · exfalso; apply hX0; rw [hX, h0]; simp
    · exact h0
  set N : ℕ → ℕ := fun s => 3 ^ (w - 1 - s) * 2 ^ (s * A / r) with hN
  have hterm : ∀ s ∈ range w, |(3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ (α (k + s) - m) - 2 ^ ((k + s) * A / r - m))| ≤
      2 ^ (2 * h + 1) * (N s : ℤ) := by
    intro s hs
    have hs' := mem_range.mp hs
    have hcs : (k + s) * A / r ≤ k * A / r + s * A / r + 1 := by
      rw [add_mul]; exact div_add_le _ _ _ hr0
    have hu := hup s hs'
    have hd := hdn s hs'
    have hx1 : α (k + s) - m ≤ s * A / r + (2 * h + 1) ∧
        (k + s) * A / r - m ≤ s * A / r + (2 * h + 1) := by
      generalize s * A / r = Z at hcs ⊢
      omega
    have hb := abs_two_pow_sub_le (x := α (k + s) - m)
      (y := (k + s) * A / r - m) (z := s * A / r + (2 * h + 1)) hx1.1 hx1.2
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ (w - 1 - s))]
    calc (3 : ℤ) ^ (w - 1 - s) * |(2 : ℤ) ^ (α (k + s) - m) - 2 ^ ((k + s) * A / r - m)|
        ≤ 3 ^ (w - 1 - s) * 2 ^ (s * A / r + (2 * h + 1)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 ^ (2 * h + 1) * (N s : ℤ) := by simp only [hN]; push_cast; rw [pow_add]; ring
  obtain ⟨s0, hs0, hmax⟩ := exists_max_image (range w) N (nonempty_range_iff.mpr (by omega))
  have hXle : |X| ≤ (w * 2 ^ (2 * h + 1) * N s0 : ℕ) := by
    calc |X| ≤ ∑ s ∈ range w, |(3 : ℤ) ^ (w - 1 - s) *
          ((2 : ℤ) ^ (α (k + s) - m) - 2 ^ ((k + s) * A / r - m))| :=
          by rw [hX]; exact abs_sum_le_sum_abs _ _
      _ ≤ ∑ s ∈ range w, (2 ^ (2 * h + 1) * (N s0 : ℤ)) := by
          apply sum_le_sum; intro s hs
          refine (hterm s hs).trans ?_
          have := hmax s hs
          have : (N s : ℤ) ≤ N s0 := by exact_mod_cast this
          exact mul_le_mul_of_nonneg_left this (by positivity)
      _ = (w * 2 ^ (2 * h + 1) * N s0 : ℕ) := by
          rw [sum_const, card_range, nsmul_eq_mul]; push_cast; ring
  have hNr : N s0 ^ r ≤ 2 ^ ((w - 1) * A) := by
    have hs0' := mem_range.mp hs0
    simp only [hN]
    rw [mul_pow, ← pow_mul, ← pow_mul]
    have h3 : 3 ^ ((w - 1 - s0) * r) ≤ 2 ^ ((w - 1 - s0) * A) := by
      rw [mul_comm (w - 1 - s0) r, mul_comm (w - 1 - s0) A, pow_mul, pow_mul]
      exact Nat.pow_le_pow_left h3r _
    have h2 : 2 ^ (s0 * A / r * r) ≤ 2 ^ (s0 * A) :=
      Nat.pow_le_pow_right (by norm_num) (Nat.div_mul_le_self _ _)
    calc 3 ^ ((w - 1 - s0) * r) * 2 ^ (s0 * A / r * r)
        ≤ 2 ^ ((w - 1 - s0) * A) * 2 ^ (s0 * A) := Nat.mul_le_mul h3 h2
      _ = 2 ^ ((w - 1) * A) := by
          rw [← pow_add]; congr 1
          rw [← add_mul]; congr 1; omega
  have hlt : w * 2 ^ (2 * h + 1) * N s0 < 2 ^ (A - A') := by
    rw [← Nat.pow_lt_pow_iff_left (show r ≠ 0 by omega), mul_pow, ← pow_mul]
    calc (w * 2 ^ (2 * h + 1)) ^ r * N s0 ^ r ≤ (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * A) :=
          Nat.mul_le_mul_left _ hNr
      _ < 2 ^ ((A - A') * r) := hW
  have hXS : |X| < S := by
    calc |X| ≤ (w * 2 ^ (2 * h + 1) * N s0 : ℕ) := hXle
      _ < (S : ℤ) := by exact_mod_cast (lt_of_lt_of_le hlt hUS)
  exact not_dvd_of_abs_lt hX0 hXS hSX

/-- Index `j < r` lies in the cyclic arc `[k, k + w)` mod `r`. -/
def inArc (r k w j : ℕ) : Prop := (k ≤ j ∧ j < k + w) ∨ j + r < k + w

instance (r k w j : ℕ) : Decidable (inArc r k w j) := by unfold inArc; infer_instance

/-- Partial sums of `v` extended past `r` by `a_{j+r} = a_j + A`. -/
def ext (r A : ℕ) (v : ℕ → ℕ) (j : ℕ) : ℕ := if j < r then psum v j else psum v (j - r) + A

theorem ext_lt {r A j : ℕ} (v : ℕ → ℕ) (h : j < r) : ext r A v j = psum v j := by
  simp [ext, h]

theorem ext_add {r A : ℕ} (v : ℕ → ℕ) (i : ℕ) : ext r A v (i + r) = psum v i + A := by
  simp [ext]

theorem gamma_shift {r A : ℕ} (hr0 : 0 < r) (i : ℕ) : (i + r) * A / r = i * A / r + A := by
  rw [add_mul, Nat.add_mul_div_left _ _ hr0]

theorem psum_succ (v : ℕ → ℕ) (j : ℕ) : psum v (j + 1) = psum v j + v j := by
  unfold psum; rw [sum_range_succ]

/-- **T1: arc theorem for `gcd(A, r) ≥ 2`.** Let `d = gcd(A, r) ≥ 2`,
`3^r + 1 < 2^A`, and let `v` have entries `≥ 1` below `r` and `psum v r = A`. Suppose its partial
sums agree with those of `chr r A` outside the *cyclic* arc `[k, k+w)` mod `r` (`k < r`,
`w ≤ r`), differ from them by at most `h` everywhere, and differ somewhere. If
`(w 2^{2h+1})^r 2^{(w-1)A} < 2^{(A - A/d) r}`, then `(2^A - 3^r) ∤ B(v)`.
Proof: non-wrapping arcs are the window theorem of `NormWindow`. For a wrapping arc put `t = k + w - r`;
modulo Solomon's cofactor `S_d` (`S_d ∣ 2^A - 3^r`, `S_d ∣ B(chr)`; Solomon 2026, Prop. 6.3)
`3^t (B(v) - B(chr)) ≡ X`, the window sum of the extended sequence `a_{j+r} = a_j + A` over
`[k, k+w)` (exact identity `X = 3^t Δ + (2^A - 3^r) W`), and `window_core` applies. -/
theorem no_cycle_arc_noncoprime (r A : ℕ) (hd : 2 ≤ Nat.gcd A r) (hq : 3 ^ r + 1 < 2 ^ A)
    (k w h : ℕ) (hk : k < r) (hwr : w ≤ r)
    (hW : (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * A) < 2 ^ ((A - A / Nat.gcd A r) * r))
    (v : ℕ → ℕ) (hv1 : ∀ i < r, 1 ≤ v i) (hsum : psum v r = A)
    (hout : ∀ j < r, ¬ inArc r k w j → psum v j = psum (NormGoal.chr r A) j)
    (hup : ∀ j < r, psum v j ≤ psum (NormGoal.chr r A) j + h)
    (hdn : ∀ j < r, psum (NormGoal.chr r A) j ≤ psum v j + h)
    (hne : ∃ j < r, psum v j ≠ psum (NormGoal.chr r A) j) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdiv
  have hr0 : 0 < r := by omega
  by_cases hkw : k + w ≤ r
  · exact no_cycle_window_noncoprime r A hd hq k w h hkw hW v (fun i hi => hv1 i (by omega))
      (fun j hj hj' => hout j hj (by unfold inArc; omega)) hup hdn hne hdiv
  have hAr := r_lt_A hq
  obtain ⟨r', A', hr', hA', hr'0⟩ := gcd_decomp (A := A) hr0
  set d := Nat.gcd A r with hd_def
  obtain ⟨hS1, hS2, hS3, hSq, hSB⟩ :=
    solomon_factor (d := d) (r' := r') (A' := A') hd hr'0 (by rw [← hr', ← hA']; exact hq)
  rw [← hr', ← hA'] at hSq hSB
  set S := Sg (2 ^ A') (3 ^ r') d with hSdef
  have hc : ∀ j, psum (NormGoal.chr r A) j = j * A / r := fun j => psum_chr j
  have hSD : (S : ℤ) ∣ (Bnum r v : ℤ) - Bnum r (NormGoal.chr r A) :=
    dvd_sub (Int.natCast_dvd_natCast.mpr (dvd_trans hSq hdiv)) (Int.natCast_dvd_natCast.mpr hSB)
  have hSq' : (S : ℤ) ∣ (2 : ℤ) ^ A - 3 ^ r := by
    have := Int.natCast_dvd_natCast.mpr hSq
    rw [Nat.cast_sub (by omega : 3 ^ r ≤ 2 ^ A)] at this
    push_cast at this; exact this
  set t := k + w - r with ht
  have ht_le : t ≤ k := by omega
  have hw' : w = (r - k) + t := by omega
  set E : ℕ → ℤ := fun j => (2 : ℤ) ^ psum v j - 2 ^ (j * A / r) with hE
  have hΔ : (Bnum r v : ℤ) - Bnum r (NormGoal.chr r A) =
      ∑ j ∈ range t, (3 : ℤ) ^ (r - 1 - j) * E j +
      ∑ s ∈ range (r - k), (3 : ℤ) ^ (r - 1 - (k + s)) * E (k + s) := by
    rw [cast_Bnum, cast_Bnum, ← sum_sub_distrib]
    have hsplit := Finset.sum_range_add (fun j => (3 : ℤ) ^ (r - 1 - j) * 2 ^ psum v j -
      (3 : ℤ) ^ (r - 1 - j) * 2 ^ psum (NormGoal.chr r A) j) k (r - k)
    rw [show k + (r - k) = r by omega] at hsplit
    rw [hsplit]
    congr 1
    · symm
      rw [← sum_subset (s₁ := range t) (s₂ := range k)]
      · apply sum_congr rfl; intro j _; simp only [hE, hc]; ring
      · intro j hj; simp only [mem_range] at hj ⊢; omega
      · intro j hj hj'
        simp only [mem_range] at hj hj'
        rw [hout j (by omega) (by unfold inArc; omega), sub_self]
    · apply sum_congr rfl; intro j _; simp only [hE, hc]; ring
  have hXeq : ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ ext r A v (k + s) - 2 ^ ((k + s) * A / r)) =
      3 ^ t * ∑ s ∈ range (r - k), (3 : ℤ) ^ (r - 1 - (k + s)) * E (k + s) +
      2 ^ A * ∑ j ∈ range t, (3 : ℤ) ^ (t - 1 - j) * E j := by
    have hsplit := Finset.sum_range_add (fun s => (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ ext r A v (k + s) - 2 ^ ((k + s) * A / r))) (r - k) t
    rw [← hw'] at hsplit
    rw [hsplit, mul_sum, mul_sum]
    congr 1
    · apply sum_congr rfl; intro s hs; have hs' := mem_range.mp hs
      rw [ext_lt v (by omega)]
      have e3 : (3 : ℤ) ^ (w - 1 - s) = 3 ^ t * 3 ^ (r - 1 - (k + s)) := by
        rw [← pow_add]; congr 1; omega
      rw [e3]; simp only [hE]; ring
    · apply sum_congr rfl; intro j hj; have hj' := mem_range.mp hj
      rw [show k + (r - k + j) = j + r by omega, ext_add, gamma_shift hr0,
        show w - 1 - (r - k + j) = t - 1 - j by omega]
      simp only [hE]; rw [pow_add, pow_add]; ring
  have hfold : (3 : ℤ) ^ t * ∑ j ∈ range t, (3 : ℤ) ^ (r - 1 - j) * E j =
      3 ^ r * ∑ j ∈ range t, (3 : ℤ) ^ (t - 1 - j) * E j := by
    rw [mul_sum, mul_sum]; apply sum_congr rfl; intro j hj; have := mem_range.mp hj
    rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
  have hSX : (S : ℤ) ∣ ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ ext r A v (k + s) - 2 ^ ((k + s) * A / r)) := by
    rw [hΔ] at hSD
    rw [hXeq]
    have : (3 : ℤ) ^ t * ∑ s ∈ range (r - k), (3 : ℤ) ^ (r - 1 - (k + s)) * E (k + s) +
        2 ^ A * ∑ j ∈ range t, (3 : ℤ) ^ (t - 1 - j) * E j =
        3 ^ t * (∑ j ∈ range t, (3 : ℤ) ^ (r - 1 - j) * E j +
          ∑ s ∈ range (r - k), (3 : ℤ) ^ (r - 1 - (k + s)) * E (k + s)) +
        (2 ^ A - 3 ^ r) * ∑ j ∈ range t, (3 : ℤ) ^ (t - 1 - j) * E j := by
      linear_combination (-1 : ℤ) * hfold
    rw [this]
    exact dvd_add (dvd_mul_of_dvd_right hSD _) (dvd_mul_of_dvd_left hSq' _)
  -- cofactor size
  have hAd : A / d = A' := by
    rw [hA']; exact Nat.mul_div_cancel_left _ (by omega)
  have hUS : 2 ^ (A - A / d) ≤ S := by
    obtain ⟨e, he⟩ : ∃ e, d = e + 2 := ⟨d - 2, by omega⟩
    have := Sg_ge_two (2 ^ A') (3 ^ r') e
    have hA2 : A - A / d = A' * (e + 1) := by
      rw [hAd]
      have : A = A' * (e + 1) + A' := by rw [hA', he]; ring
      omega
    rw [hA2, pow_mul, hSdef, he]
    omega
  refine window_core (r := r) (A := A) (A' := A / d) (h := h) (k := k) (w := w) (S := S) hr0
    hAr.le (by omega) hS2 hUS hW (ext r A v) ?_ ?_ ?_ ?_ hSX
  · -- strict monotonicity
    intro s hs
    rcases lt_trichotomy (k + s + 1) r with h1 | h1 | h1
    · rw [ext_lt v (by omega), ext_lt v h1, psum_succ]
      have := hv1 (k + s) (by omega); omega
    · have e0 := ext_add (r := r) (A := A) v 0
      rw [zero_add] at e0
      rw [ext_lt v (by omega), h1, e0]
      have e := psum_succ v (k + s)
      rw [h1, hsum] at e
      have := hv1 (k + s) (by omega)
      have p0 : psum v 0 = 0 := by simp [psum]
      omega
    · obtain ⟨i, hi⟩ : ∃ i, k + s = i + r := ⟨k + s - r, by omega⟩
      rw [hi, ext_add, show i + r + 1 = (i + 1) + r by omega, ext_add, psum_succ]
      have := hv1 i (by omega); omega
  · intro s hs
    by_cases h1 : k + s < r
    · rw [ext_lt v h1, ← hc]; exact hup _ h1
    · obtain ⟨i, hi⟩ : ∃ i, k + s = i + r := ⟨k + s - r, by omega⟩
      rw [hi, ext_add, gamma_shift hr0, ← hc]
      have := hup i (by omega); omega
  · intro s hs
    by_cases h1 : k + s < r
    · rw [ext_lt v h1, ← hc]; exact hdn _ h1
    · obtain ⟨i, hi⟩ : ∃ i, k + s = i + r := ⟨k + s - r, by omega⟩
      rw [hi, ext_add, gamma_shift hr0, ← hc]
      have := hdn i (by omega); omega
  · obtain ⟨j0, hj0, hne0⟩ := hne
    have hin : inArc r k w j0 := by
      by_contra hc'; exact hne0 (hout j0 hj0 hc')
    rw [hc] at hne0
    rcases hin with ⟨h1, h2⟩ | h1
    · refine ⟨j0 - k, by omega, ?_⟩
      rw [show k + (j0 - k) = j0 by omega, ext_lt v hj0]; exact hne0
    · refine ⟨j0 + r - k, by omega, ?_⟩
      rw [show k + (j0 + r - k) = j0 + r by omega, ext_add, gamma_shift hr0]; omega

/-- Exponent bookkeeping for T2: from `(r 2^{2h+1})^{c+1} < 2^{A''}` and
`(c+1)(w-1) ≤ c r`, `w ≤ r`, get the arc hypothesis of T1 with `A = (c+2) A''`. -/
theorem hW_of_hH {r A'' c w h : ℕ} (hr : 0 < r) (hw : w ≤ r) (hcw : (c + 1) * (w - 1) ≤ c * r)
    (hH : (r * 2 ^ (2 * h + 1)) ^ (c + 1) < 2 ^ A'') :
    (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * ((c + 2) * A'')) <
      2 ^ (((c + 2) * A'' - A'') * r) := by
  rw [show (c + 2) * A'' - A'' = (c + 1) * A'' from
    Nat.sub_eq_of_eq_add (by ring)]
  apply (Nat.pow_lt_pow_iff_left (n := c + 1) (by omega)).mp
  have hB : w * 2 ^ (2 * h + 1) ≤ r * 2 ^ (2 * h + 1) := Nat.mul_le_mul_right _ hw
  calc ((w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * ((c + 2) * A''))) ^ (c + 1)
      = (w * 2 ^ (2 * h + 1)) ^ (r * (c + 1)) * 2 ^ ((c + 1) * (w - 1) * ((c + 2) * A'')) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]; congr 2; ring
    _ ≤ (r * 2 ^ (2 * h + 1)) ^ (r * (c + 1)) * 2 ^ (c * r * ((c + 2) * A'')) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hB _)
          (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hcw))
    _ = ((r * 2 ^ (2 * h + 1)) ^ (c + 1)) ^ r * 2 ^ (c * r * ((c + 2) * A'')) := by
        rw [← pow_mul, mul_comm r (c + 1)]
    _ < (2 ^ A'') ^ r * 2 ^ (c * r * ((c + 2) * A'')) :=
        Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hH (by omega)) (by positivity)
    _ = (2 ^ ((c + 1) * A'' * r)) ^ (c + 1) := by
        rw [← pow_mul, ← pow_add, ← pow_mul]; congr 1; ring

/-- The cyclic intervals `I_x = [x, x+g) mod r` containing a fixed `j < r`: at most `g` of
them. -/
theorem card_arcs_le (r g j : ℕ) (_hj : j < r) :
    ((range r).filter (fun x => inArc r x g j)).card ≤ g := by
  have hsub : (range r).filter (fun x => inArc r x g j) ⊆
      (range g).image (fun y => if y ≤ j then j - y else j + r - y) := by
    intro x hx
    rw [mem_filter, mem_range] at hx
    unfold inArc at hx
    simp only [mem_image, mem_range]
    rcases hx with ⟨hxr, ⟨h1, h2⟩ | h1⟩
    · exact ⟨j - x, by omega, by simp [show j - x ≤ j by omega]; omega⟩
    · exact ⟨j + r - x, by omega, by simp [show ¬ (j + r - x ≤ j) by omega]; omega⟩
  calc _ ≤ _ := card_le_card hsub
    _ ≤ (range g).card := card_image_le
    _ = g := card_range g

/-- **Free cyclic gap.** If `E ⊆ [0, r)` has `K ≥ 1` points and `K g < r`, some cyclic interval
`[x, x+g) mod r` (`x < r`) misses `E`. -/
theorem free_gap (r g : ℕ) (E : Finset ℕ) (hE : ∀ j ∈ E, j < r) (hKg : E.card * g < r) :
    ∃ x < r, ∀ j ∈ E, ¬ inArc r x g j := by
  by_contra hcon
  push Not at hcon
  have h1 : r ≤ ∑ x ∈ range r, (E.filter (fun j => inArc r x g j)).card := by
    calc r = ∑ x ∈ range r, 1 := by simp
      _ ≤ _ := by
        apply sum_le_sum; intro x hx
        obtain ⟨j, hj, hj'⟩ := hcon x (mem_range.mp hx)
        exact card_pos.mpr ⟨j, mem_filter.mpr ⟨hj, hj'⟩⟩
  have h2 : ∑ x ∈ range r, (E.filter (fun j => inArc r x g j)).card =
      ∑ j ∈ E, ((range r).filter (fun x => inArc r x g j)).card := by
    simp only [card_filter]; exact sum_comm
  have h3 : ∑ j ∈ E, ((range r).filter (fun x => inArc r x g j)).card ≤ E.card * g := by
    calc _ ≤ ∑ j ∈ E, g := sum_le_sum (fun j hj => card_arcs_le r g j (hE j hj))
      _ = E.card * g := by rw [sum_const, smul_eq_mul]
  omega

/-- **T2: at most `d - 1` deviating indices, any bounded height.** Let
`d = gcd(A, r) ≥ 2`, `3^r + 1 < 2^A`, and `(r 2^{2h+1})^{d-1} < 2^{A/d}`. If `v` has entries
`≥ 1` below `r`, `psum v r = A`, and its partial sums differ from those of `chr r A` at some but
at most `d - 1` indices `j < r` (all inside the finset `D`, `|D| ≤ d - 1`), each time by at most
`h`, then `(2^A - 3^r) ∤ B(v)`. Proof: `K ≤ d - 1` points on `ℤ/r` leave a free cyclic gap of
length `g = ⌊(r-1)/K⌋` (double counting, `free_gap`), so the deviations lie in an arc of length
`w = r - g` with `(d-1)(w-1) ≤ (d-2) r`; then `(r 2^{2h+1})^{d-1} < 2^{A/d}` implies T1's
hypothesis (`hW_of_hH`) and T1 applies. Positions of the sites are arbitrary (no distance
condition). -/
theorem no_cycle_few_sites_noncoprime (r A h : ℕ) (hd : 2 ≤ Nat.gcd A r)
    (hq : 3 ^ r + 1 < 2 ^ A)
    (hH : (r * 2 ^ (2 * h + 1)) ^ (Nat.gcd A r - 1) < 2 ^ (A / Nat.gcd A r))
    (v : ℕ → ℕ) (hv1 : ∀ i < r, 1 ≤ v i) (hsum : psum v r = A)
    (D : Finset ℕ) (hD : D.card ≤ Nat.gcd A r - 1)
    (hout : ∀ j < r, j ∉ D → psum v j = psum (NormGoal.chr r A) j)
    (hup : ∀ j < r, psum v j ≤ psum (NormGoal.chr r A) j + h)
    (hdn : ∀ j < r, psum (NormGoal.chr r A) j ≤ psum v j + h)
    (hne : ∃ j < r, psum v j ≠ psum (NormGoal.chr r A) j) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  have hr0 : 0 < r := by obtain ⟨j, hj, -⟩ := hne; omega
  set d := Nat.gcd A r with hd_def
  set E := (range r).filter (fun j => psum v j ≠ psum (NormGoal.chr r A) j) with hEdef
  have hEr : ∀ j ∈ E, j < r := fun j hj => mem_range.mp (mem_filter.mp hj).1
  have hED : E ⊆ D := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_filter.mp hj
    by_contra hjD; exact hj2 (hout j (mem_range.mp hj1) hjD)
  have hK1 : 0 < E.card := by
    obtain ⟨j, hj, hj'⟩ := hne
    exact card_pos.mpr ⟨j, mem_filter.mpr ⟨mem_range.mpr hj, hj'⟩⟩
  have hKd : E.card ≤ d - 1 := (card_le_card hED).trans hD
  set K := E.card with hK
  set g := (r - 1) / K with hg
  have hKg : K * g < r := by
    have := Nat.mul_div_le (r - 1) K; rw [hg]; omega
  have hKg' : r ≤ K * (g + 1) := by
    have := Nat.lt_mul_div_succ (r - 1) hK1; rw [hg]; omega
  have hgr : g < r := by
    have : g ≤ r - 1 := Nat.div_le_self _ _
    omega
  clear_value g
  obtain ⟨x, hx, hfree⟩ := free_gap r g E hEr hKg
  set k := if x + g < r then x + g else x + g - r with hk
  set w := r - g with hw
  have hkr : k < r := by rw [hk]; split_ifs <;> omega
  have hcover : ∀ j ∈ E, inArc r k w j := by
    intro j hj
    have hj1 := hEr j hj
    have hj2 := hfree j hj
    unfold inArc at hj2 ⊢
    rw [hk]; split_ifs with hc <;> omega
  clear_value k w
  obtain ⟨c, hc⟩ : ∃ c, d = c + 2 := ⟨d - 2, by omega⟩
  obtain ⟨A'', hA''⟩ : ∃ A'', A = d * A'' := Nat.gcd_dvd_left A r
  have hAd : A / d = A'' := by rw [hA'']; exact Nat.mul_div_cancel_left _ (by omega)
  have hcw : (c + 1) * (w - 1) ≤ c * r := by
    have h1 : (c + 1) * (g + 1) ≥ r := by
      have : K * (g + 1) ≤ (c + 1) * (g + 1) := Nat.mul_le_mul_right _ (by omega)
      omega
    have h2 : w - 1 = r - (g + 1) := by omega
    rw [h2, Nat.mul_sub]
    have : (c + 1) * r = c * r + r := by ring
    omega
  have hW := hW_of_hH (A'' := A'') (h := h) hr0 (show w ≤ r by omega) hcw
    (by rw [hAd, hc] at hH; simpa using hH)
  refine no_cycle_arc_noncoprime r A hd hq k w h hkr (by omega) ?_ v hv1 hsum ?_ hup hdn hne
  · rw [hAd]; rw [hA'', hc]; exact hW
  · intro j hj hj'
    by_contra hne'
    exact hj' (hcover j (mem_filter.mpr ⟨mem_range.mpr hj, hne'⟩))

section Cycle
open CollatzProof

/-- **Cycle form of T1.** No positive `T`-cycle with `r ≥ 2` odd steps and period `L`,
`gcd(L, r) ≥ 2`, has a valuation word `v` whose partial sums leave those of `chr r L` only inside
a cyclic arc `[k, k+w)` mod `r`, by at most `h`, when `(w 2^{2h+1})^r 2^{(w-1)L} < 2^{(L - L/d) r}`.
Non-vacuity (hypotheses jointly satisfiable by a valid word): `r = 122703`, `L = 194484`
(`gcd = 3`, `3^r + 1 < 2^L`, `witness_d3`), `v = chr r L` with right flips at sites `1, 3, r - 2`
(`chr` starts `1,2,1,2` and ends `1,2,2`), arc `k = r - 2`, `w = 6`, `h = 1`; this wraps, has three
sites, and is covered neither by the linear window of `NormWindow` nor by its two-site theorem. -/
theorem cycle_arc_noncoprime {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hd : 2 ≤ Nat.gcd L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (k w h : ℕ) (hk : k < r) (hwr : w ≤ r)
    (hW : (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * L) < 2 ^ ((L - L / Nat.gcd L r) * r))
    (hout : ∀ j < r, ¬ inArc r k w j → psum v j = psum (NormGoal.chr r L) j)
    (hup : ∀ j < r, psum v j ≤ psum (NormGoal.chr r L) j + h)
    (hdn : ∀ j < r, psum (NormGoal.chr r L) j ≤ psum v j + h)
    (hne : ∃ j < r, psum v j ≠ psum (NormGoal.chr r L) j) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  exact no_cycle_arc_noncoprime r L hd hq k w h hk hwr hW v hv1 hL hout hup hdn hne hdiv

/-- **Cycle form of T2.** No positive `T`-cycle with `r ≥ 2` odd steps and period `L`,
`d = gcd(L, r) ≥ 2`, `(r 2^{2h+1})^{d-1} < 2^{L/d}`, has a valuation word whose partial sums
differ from those of `chr r L` at between `1` and `d - 1` indices, each by at most `h`.
Non-vacuity: `r = 122704`, `L = 194484` (`gcd = 4`, `h ≤ 8094`; `witness_d4`), `v = chr r L`
with right flips at three separated up-sites (three deviating indices, height 1) — not covered by
`NormCofactor`'s two-site theorem. At `r = 122703`, `L = 194484` (`d = 3`) the hypothesis holds for
`h ≤ 16198` (`witness_d3`), but there two sites are already `NormCofactor`. -/
theorem cycle_few_sites_noncoprime {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hd : 2 ≤ Nat.gcd L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m) (h : ℕ)
    (hH : (r * 2 ^ (2 * h + 1)) ^ (Nat.gcd L r - 1) < 2 ^ (L / Nat.gcd L r))
    (D : Finset ℕ) (hD : D.card ≤ Nat.gcd L r - 1)
    (hout : ∀ j < r, j ∉ D → psum v j = psum (NormGoal.chr r L) j)
    (hup : ∀ j < r, psum v j ≤ psum (NormGoal.chr r L) j + h)
    (hdn : ∀ j < r, psum (NormGoal.chr r L) j ≤ psum v j + h)
    (hne : ∃ j < r, psum v j ≠ psum (NormGoal.chr r L) j) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  exact no_cycle_few_sites_noncoprime r L h hd hq hH v hv1 hL D hD hout hup hdn hne hdiv

end Cycle

/-- Numerical non-vacuity certificate (`d = 3`): `gcd(194484, 122703) = 3`,
`3^122703 + 1 < 2^194484`, and T2's height hypothesis holds with `h = 16198`. -/
theorem witness_d3 : Nat.gcd 194484 122703 = 3 ∧ 3 ^ 122703 + 1 < 2 ^ 194484 ∧
    (122703 * 2 ^ (2 * 16198 + 1)) ^ (Nat.gcd 194484 122703 - 1) <
      2 ^ (194484 / Nat.gcd 194484 122703) := by decide +kernel

/-- Numerical non-vacuity certificate (`d = 4`): `gcd(194484, 122704) = 4`,
`3^122704 + 1 < 2^194484`, and T2's height hypothesis holds with `h = 8094`. -/
theorem witness_d4 : Nat.gcd 194484 122704 = 4 ∧ 3 ^ 122704 + 1 < 2 ^ 194484 ∧
    (122704 * 2 ^ (2 * 8094 + 1)) ^ (Nat.gcd 194484 122704 - 1) <
      2 ^ (194484 / Nat.gcd 194484 122704) := by decide +kernel

end Collatz.NormArc

#print axioms Collatz.NormArc.seq_inj
#print axioms Collatz.NormArc.window_core
#print axioms Collatz.NormArc.no_cycle_arc_noncoprime
#print axioms Collatz.NormArc.cycle_arc_noncoprime
#print axioms Collatz.NormArc.no_cycle_few_sites_noncoprime
#print axioms Collatz.NormArc.cycle_few_sites_noncoprime
#print axioms Collatz.NormArc.witness_d3
#print axioms Collatz.NormArc.witness_d4
