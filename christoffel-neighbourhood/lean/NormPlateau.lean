import NormArc
import NormCycleAll

/-!
# plateaus — constant offsets are invisible modulo Solomon's cofactor

Notation: `d = gcd(A, r) ≥ 2`, `chr r A` the lower Christoffel word (partial sums
`c_j = ⌊jA/r⌋`), `B(v) = Σ_{j<r} 3^{r-1-j} 2^{psum v j}`, `q = 2^A - 3^r`, `S_d` Solomon's
cofactor (Solomon 2026, Zenodo 22220730, Prop. 6.3: `S_d ∣ q`, `S_d ∣ B(chr)`, `gcd(S_d,6) = 1`,
`S_d ≥ 2^{A - A/d}`). The *deviation* of a word `v` is `ε_j = psum v j - c_j` (indexed by
partial-sum indices `j`, NOT by letter/swap positions); `ε_0 = ε_r = 0`, so `ε` lives on `ℤ/r`.

Key observation: for any constants `e₁, e₂`, `S_d ∣ 2^{e₁} B(v) - 2^{e₂} B(chr)
= Σ_j 3^{r-1-j}(2^{psum v j + e₁} - 2^{c_j + e₂})` whenever `q ∣ B(v)`. So only the partial-sum
indices where `ε` differs from a constant `κ = e₂ - e₁` matter, not where it differs from `0`.

* `window_core_shift`: `NormArc`'s `NormArc.window_core` against the comparison sequence `c_j + e`.
* **T1** `no_cycle_offset_arc_noncoprime`: `NormArc`'s cyclic arc theorem with a constant offset —
  `ε ≡ κ` outside a cyclic arc of partial-sum indices `[k, k+w)`, `|ε - κ| ≤ h`, and
  `(w 2^{2h+1})^r 2^{(w-1)A} < 2^{(A-A/d) r}` imply `q ∤ B(v)`.
* **T2** `no_cycle_few_levels_noncoprime`: if `ε` changes value at fewer than `d` cyclic
  positions (a set `P`) and `|ε| ≤ H`, with `(r 2^{4H+1})^{|P|} < 2^{(d-|P|)A/d}`, then
  `q ∤ B(v)` (pigeonhole: a constant run of length `≥ r/|P|`; its complement is an arc; T1).
  This covers `K` simultaneous slides at arbitrary distances when `2K ≤ d - 1`.
* **T3** (DIRECTIVES 2(c), one unit slid any distance, non-coprime case):
  `no_cycle_slide_noncoprime3` — for `gcd(A, r) ≥ 3` and `(32r)^6 < 2^A`, NO word
  `slide (chr r A) a b` (any `a ≠ b < r`, `chr a ≥ 2`) has `q ∣ B`;
  `no_cycle_slide_noncoprime` — any `d ≥ 2`, if the arc condition (h = 1) holds at `D = |a-b|`
  or at `r - D` (the deviation is `∓1` exactly on the `D` indices between `a` and `b`, and
  constant on the other `r - D`). For `d = 2` this leaves a band of middle distances only:
  `r = 40902, A = 64832`: `D ∈ [20442, 20460]` (19 values); `r = 122704, A = 194482`: 21 values;
  `r = 10^6, A = 1584966`: 25 values.
* Cycle forms `cycle_offset_arc_noncoprime`, `cycle_few_levels_noncoprime`,
  `cycle_slide_noncoprime3` (only `gcd(L, r) ≥ 3` and `m ≠ 1`; `r ≥ 40901` from
  `NormCycleAll.cycle_params` gives `(32r)^6 < 2^L` via `pow6`), `cycle_slide_noncoprime`.

Scope: word-level / cycle-equation exclusions for NON-coprime `(r, A)` only. The coprime
case of 2(c) — the generic case — is not covered (S_d methods are empty there). The `d = 2` band
is a method gap, not a counterexample (all 402 tested `d = 2` pairs, `r < 900`: no slide at any
distance even has `S_2 ∣ Δ`). Numerics: 1.8·10^6 small words with `≤ d - 1`
level changes, no `q ∣ B`. Prior art: Knight, Lebel, Mghirbi, Solomon,
Fernández–Ibáñez (arXiv 2607.24844).

Scope wording: the slide theorems exclude a cycle whose valuation word, read from
the chosen start `m`, is *a slide of `chr r L`*; they do not say "any perturbation of a balanced
cycle". Slides of rotations of chr are covered by choosing another start on the cycle
(`rot^k(slide(chr, a, b)) = slide(rot^k chr, a-k, b-k)`): a remark, not a proved statement here.
The `d = 2` case is NOT settled: about 20 middle distances remain open, and `NormFold`
does not close them either (every column is bad there).
-/

namespace Collatz.NormPlateau
open Collatz.NormGoal Collatz.NormReduce Collatz.NormAll
  Collatz.NormCofactor Collatz.NormWindow Collatz.NormArc Finset

/-- `NormArc.window_core` with comparison sequence `⌊jA/r⌋ + e`: an odd `S ≥ 2^{A-A'}` cannot
divide the nonzero window sum `Σ_{s<w} 3^{w-1-s}(2^{α(k+s)} - 2^{⌊(k+s)A/r⌋ + e})` when `α` is
strictly increasing on the window, within `h` of the comparison, not equal to it, and
`(w 2^{2h+1})^r 2^{(w-1)A} < 2^{(A-A')r}`. -/
theorem window_core_shift {r A A' h k w S e : ℕ} (hr0 : 0 < r) (hAr : r ≤ A) (h3r : 3 ^ r ≤ 2 ^ A)
    (hS2 : Nat.Coprime 2 S) (hUS : 2 ^ (A - A') ≤ S)
    (hW : (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * A) < 2 ^ ((A - A') * r))
    (α : ℕ → ℕ) (hmonoα : ∀ s, s + 1 < w → α (k + s) < α (k + s + 1))
    (hup : ∀ s < w, α (k + s) ≤ (k + s) * A / r + e + h)
    (hdn : ∀ s < w, (k + s) * A / r + e ≤ α (k + s) + h)
    (hne : ∃ s < w, α (k + s) ≠ (k + s) * A / r + e)
    (hdvd : (S : ℤ) ∣ ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ α (k + s) - 2 ^ ((k + s) * A / r + e))) : False := by
  set m := k * A / r + e - h with hm
  have hmono : ∀ s, k * A / r ≤ (k + s) * A / r := by
    intro s; exact Nat.div_le_div_right (Nat.mul_le_mul_right _ (by omega))
  have hγs : ∀ j, j * A / r + 1 ≤ (j + 1) * A / r := by
    intro j
    have : j * A / r + 1 = (j * A + r) / r := by rw [Nat.add_div_right _ hr0]
    rw [this]; apply Nat.div_le_div_right; rw [add_mul, one_mul]; omega
  set X : ℤ := ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
    ((2 : ℤ) ^ (α (k + s) - m) - 2 ^ ((k + s) * A / r + e - m)) with hX
  have hTX : ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ α (k + s) - 2 ^ ((k + s) * A / r + e)) = 2 ^ m * X := by
    rw [hX, mul_sum]
    apply sum_congr rfl
    intro s hs
    have hs' := mem_range.mp hs
    have h1 := hdn s hs'
    have h2 := hmono s
    have hma : m ≤ α (k + s) := by
      generalize (k + s) * A / r = Y at h1 h2; generalize k * A / r = Q at h2 hm; omega
    have hmc : m ≤ (k + s) * A / r + e := by
      generalize (k + s) * A / r = Y at h1 h2 ⊢; generalize k * A / r = Q at h2 hm; omega
    have ea : (2 : ℤ) ^ α (k + s) = 2 ^ m * 2 ^ (α (k + s) - m) := by
      rw [← pow_add]; congr 1; omega
    have ec : (2 : ℤ) ^ ((k + s) * A / r + e) = 2 ^ m * 2 ^ ((k + s) * A / r + e - m) := by
      rw [← pow_add]; congr 1; omega
    rw [ea, ec]; ring
  have hX0 : X ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at hTX
    simp only [mul_sub, sum_sub_distrib, sub_eq_zero] at hTX
    have hN : ∑ s ∈ range w, 3 ^ (w - 1 - s) * 2 ^ α (k + s) =
        ∑ s ∈ range w, 3 ^ (w - 1 - s) * 2 ^ ((k + s) * A / r + e) := by exact_mod_cast hTX
    obtain ⟨s0, hs0, hne0⟩ := hne
    exact hne0 (seq_inj (f := fun s => α (k + s)) (g := fun s => (k + s) * A / r + e)
      (fun s hs => hmonoα s hs)
      (fun s _ => by
        have := hγs (k + s); simp only [← add_assoc]
        generalize (k + s) * A / r = Y at this ⊢; generalize (k + s + 1) * A / r = Q at this ⊢
        omega) hN s0 hs0)
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
      ((2 : ℤ) ^ (α (k + s) - m) - 2 ^ ((k + s) * A / r + e - m))| ≤
      2 ^ (2 * h + 1) * (N s : ℤ) := by
    intro s hs
    have hs' := mem_range.mp hs
    have hcs : (k + s) * A / r ≤ k * A / r + s * A / r + 1 := by
      rw [add_mul]; exact div_add_le _ _ _ hr0
    have hu := hup s hs'
    have hd := hdn s hs'
    have hx1 : α (k + s) - m ≤ s * A / r + (2 * h + 1) ∧
        (k + s) * A / r + e - m ≤ s * A / r + (2 * h + 1) := by
      generalize s * A / r = Z at hcs ⊢
      generalize (k + s) * A / r = Y at hcs hu hd ⊢
      generalize k * A / r = Q at hcs hm ⊢
      omega
    have hb := abs_two_pow_sub_le (x := α (k + s) - m)
      (y := (k + s) * A / r + e - m) (z := s * A / r + (2 * h + 1)) hx1.1 hx1.2
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℤ) < 3 ^ (w - 1 - s))]
    calc (3 : ℤ) ^ (w - 1 - s) * |(2 : ℤ) ^ (α (k + s) - m) - 2 ^ ((k + s) * A / r + e - m)|
        ≤ 3 ^ (w - 1 - s) * 2 ^ (s * A / r + (2 * h + 1)) :=
          mul_le_mul_of_nonneg_left hb (by positivity)
      _ = 2 ^ (2 * h + 1) * (N s : ℤ) := by simp only [hN]; push_cast; rw [pow_add]; ring
  obtain ⟨s0, hs0, hmax⟩ := exists_max_image (range w) N (nonempty_range_iff.mpr (by omega))
  have hXle : |X| ≤ (w * 2 ^ (2 * h + 1) * N s0 : ℕ) := by
    calc |X| ≤ ∑ s ∈ range w, |(3 : ℤ) ^ (w - 1 - s) *
          ((2 : ℤ) ^ (α (k + s) - m) - 2 ^ ((k + s) * A / r + e - m))| :=
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

/-- **T1: offset arc theorem, `gcd(A, r) ≥ 2`.** Let `d = gcd(A,r) ≥ 2`,
`3^r + 1 < 2^A`, `v` with entries `≥ 1` below `r` and `psum v r = A`, and `e₁, e₂ ∈ ℕ`. Suppose
`psum v j + e₁ = ⌊jA/r⌋ + e₂` for every partial-sum index `j < r` outside the cyclic arc
`[k, k+w)` mod `r`, the two sides differ by at most `h` everywhere and differ somewhere. If
`(w 2^{2h+1})^r 2^{(w-1)A} < 2^{(A - A/d) r}`, then `(2^A - 3^r) ∤ B(v)`. (`e₁ = e₂ = 0` is
`NormArc`'s `no_cycle_arc_noncoprime`.) Proof: `S_d` divides `2^{e₁}B(v) - 2^{e₂}B(chr)`, which is
supported on the arc; non-wrapping arcs factor out `3^{r-k-w}`, wrapping arcs fold via
`X = 3^t Δ' + (2^A - 3^r) W`; then `window_core_shift`. -/
theorem no_cycle_offset_arc_noncoprime (r A : ℕ) (hd : 2 ≤ Nat.gcd A r) (hq : 3 ^ r + 1 < 2 ^ A)
    (k w h e₁ e₂ : ℕ) (hk : k < r) (hwr : w ≤ r)
    (hW : (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * A) < 2 ^ ((A - A / Nat.gcd A r) * r))
    (v : ℕ → ℕ) (hv1 : ∀ i < r, 1 ≤ v i) (hsum : psum v r = A)
    (hout : ∀ j < r, ¬ inArc r k w j → psum v j + e₁ = psum (NormGoal.chr r A) j + e₂)
    (hup : ∀ j < r, psum v j + e₁ ≤ psum (NormGoal.chr r A) j + e₂ + h)
    (hdn : ∀ j < r, psum (NormGoal.chr r A) j + e₂ ≤ psum v j + e₁ + h)
    (hne : ∃ j < r, psum v j + e₁ ≠ psum (NormGoal.chr r A) j + e₂) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  intro hdiv
  have hr0 : 0 < r := by omega
  have hAr := r_lt_A hq
  obtain ⟨r', A', hr', hA', hr'0⟩ := gcd_decomp (A := A) hr0
  set d := Nat.gcd A r with hd_def
  obtain ⟨hS1, hS2, hS3, hSq, hSB⟩ :=
    solomon_factor (d := d) (r' := r') (A' := A') hd hr'0 (by rw [← hr', ← hA']; exact hq)
  rw [← hr', ← hA'] at hSq hSB
  set S := Sg (2 ^ A') (3 ^ r') d with hSdef
  have hc : ∀ j, psum (NormGoal.chr r A) j = j * A / r := fun j => psum_chr j
  set E : ℕ → ℤ := fun j => (2 : ℤ) ^ (psum v j + e₁) - 2 ^ (j * A / r + e₂) with hE
  have hEz : ∀ j < r, ¬ inArc r k w j → E j = 0 := by
    intro j hj hj'; simp only [hE]; rw [hout j hj hj', hc, sub_self]
  have hΔ' : (2 : ℤ) ^ e₁ * (Bnum r v : ℤ) - 2 ^ e₂ * Bnum r (NormGoal.chr r A) =
      ∑ j ∈ range r, (3 : ℤ) ^ (r - 1 - j) * E j := by
    rw [cast_Bnum, cast_Bnum, mul_sum, mul_sum, ← sum_sub_distrib]
    apply sum_congr rfl; intro j _; simp only [hE, hc]; rw [pow_add, pow_add]; ring
  have hSD : (S : ℤ) ∣ ∑ j ∈ range r, (3 : ℤ) ^ (r - 1 - j) * E j := by
    rw [← hΔ']
    exact dvd_sub (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr (dvd_trans hSq hdiv)) _)
      (dvd_mul_of_dvd_right (Int.natCast_dvd_natCast.mpr hSB) _)
  have hSq' : (S : ℤ) ∣ (2 : ℤ) ^ A - 3 ^ r := by
    have := Int.natCast_dvd_natCast.mpr hSq
    rw [Nat.cast_sub (by omega : 3 ^ r ≤ 2 ^ A)] at this
    push_cast at this; exact this
  have hsplitr : ∑ j ∈ range r, (3 : ℤ) ^ (r - 1 - j) * E j =
      ∑ j ∈ range k, (3 : ℤ) ^ (r - 1 - j) * E j +
      ∑ s ∈ range (r - k), (3 : ℤ) ^ (r - 1 - (k + s)) * E (k + s) := by
    have hsplit := Finset.sum_range_add (fun j => (3 : ℤ) ^ (r - 1 - j) * E j) k (r - k)
    rw [show k + (r - k) = r by omega] at hsplit
    exact hsplit
  have hSX : (S : ℤ) ∣ ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
      ((2 : ℤ) ^ (ext r A v (k + s) + e₁) - 2 ^ ((k + s) * A / r + e₂)) := by
    by_cases hkw : k + w ≤ r
    · -- no wrap
      have h0 : ∑ j ∈ range k, (3 : ℤ) ^ (r - 1 - j) * E j = 0 := by
        apply sum_eq_zero; intro j hj; have := mem_range.mp hj
        rw [hEz j (by omega) (by unfold inArc; omega), mul_zero]
      have hsplit2 := Finset.sum_range_add (fun s => (3 : ℤ) ^ (r - 1 - (k + s)) * E (k + s))
        w (r - k - w)
      rw [show w + (r - k - w) = r - k by omega] at hsplit2
      have h0' : ∑ s ∈ range (r - k - w), (3 : ℤ) ^ (r - 1 - (k + (w + s))) * E (k + (w + s))
          = 0 := by
        apply sum_eq_zero; intro j hj; have := mem_range.mp hj
        rw [hEz (k + (w + j)) (by omega) (by unfold inArc; omega), mul_zero]
      rw [hsplitr, h0, zero_add, hsplit2, h0', add_zero] at hSD
      have hfac : ∑ s ∈ range w, (3 : ℤ) ^ (r - 1 - (k + s)) * E (k + s) =
          3 ^ (r - k - w) * ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
            ((2 : ℤ) ^ (ext r A v (k + s) + e₁) - 2 ^ ((k + s) * A / r + e₂)) := by
        rw [mul_sum]; apply sum_congr rfl; intro s hs; have := mem_range.mp hs
        rw [ext_lt v (by omega)]
        have e3 : (3 : ℤ) ^ (r - 1 - (k + s)) = 3 ^ (r - k - w) * 3 ^ (w - 1 - s) := by
          rw [← pow_add]; congr 1; omega
        rw [e3]; simp only [hE]; ring
      rw [hfac] at hSD
      have c3 : IsCoprime (S : ℤ) 3 := by
        have := Nat.isCoprime_iff_coprime.mpr hS3.symm; simpa using this
      exact (c3.pow_right (n := r - k - w)).dvd_of_dvd_mul_left hSD
    · -- wrap
      set t := k + w - r with ht
      have hw' : w = (r - k) + t := by omega
      have hΔ : ∑ j ∈ range r, (3 : ℤ) ^ (r - 1 - j) * E j =
          ∑ j ∈ range t, (3 : ℤ) ^ (r - 1 - j) * E j +
          ∑ s ∈ range (r - k), (3 : ℤ) ^ (r - 1 - (k + s)) * E (k + s) := by
        rw [hsplitr]
        congr 1
        symm
        rw [← sum_subset (s₁ := range t) (s₂ := range k)]
        · intro j hj; simp only [mem_range] at hj ⊢; omega
        · intro j hj hj'
          simp only [mem_range] at hj hj'
          rw [hEz j (by omega) (by unfold inArc; omega), mul_zero]
      have hXeq : ∑ s ∈ range w, (3 : ℤ) ^ (w - 1 - s) *
          ((2 : ℤ) ^ (ext r A v (k + s) + e₁) - 2 ^ ((k + s) * A / r + e₂)) =
          3 ^ t * ∑ s ∈ range (r - k), (3 : ℤ) ^ (r - 1 - (k + s)) * E (k + s) +
          2 ^ A * ∑ j ∈ range t, (3 : ℤ) ^ (t - 1 - j) * E j := by
        have hsplit := Finset.sum_range_add (fun s => (3 : ℤ) ^ (w - 1 - s) *
          ((2 : ℤ) ^ (ext r A v (k + s) + e₁) - 2 ^ ((k + s) * A / r + e₂))) (r - k) t
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
            show w - 1 - (r - k + j) = t - 1 - j by omega,
            show psum v j + A + e₁ = (psum v j + e₁) + A by ring,
            show j * A / r + A + e₂ = (j * A / r + e₂) + A by ring]
          simp only [hE]; rw [pow_add, pow_add]; ring
      have hfold : (3 : ℤ) ^ t * ∑ j ∈ range t, (3 : ℤ) ^ (r - 1 - j) * E j =
          3 ^ r * ∑ j ∈ range t, (3 : ℤ) ^ (t - 1 - j) * E j := by
        rw [mul_sum, mul_sum]; apply sum_congr rfl; intro j hj; have := mem_range.mp hj
        rw [← mul_assoc, ← mul_assoc, ← pow_add, ← pow_add]; congr 2; omega
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
  refine window_core_shift (r := r) (A := A) (A' := A / d) (h := h) (k := k) (w := w) (S := S)
    (e := e₂) hr0 hAr.le (by omega) hS2 hUS hW (fun j => ext r A v j + e₁) ?_ ?_ ?_ ?_ hSX
  · -- strict monotonicity
    intro s hs
    show ext r A v (k + s) + e₁ < ext r A v (k + s + 1) + e₁
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
    show ext r A v (k + s) + e₁ ≤ (k + s) * A / r + e₂ + h
    by_cases h1 : k + s < r
    · rw [ext_lt v h1, ← hc]; exact hup _ h1
    · obtain ⟨i, hi⟩ : ∃ i, k + s = i + r := ⟨k + s - r, by omega⟩
      rw [hi, ext_add, gamma_shift hr0, ← hc]
      have := hup i (by omega); omega
  · intro s hs
    show (k + s) * A / r + e₂ ≤ ext r A v (k + s) + e₁ + h
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
      show ext r A v (k + (j0 - k)) + e₁ ≠ (k + (j0 - k)) * A / r + e₂
      rw [show k + (j0 - k) = j0 by omega, ext_lt v hj0]; exact hne0
    · refine ⟨j0 + r - k, by omega, ?_⟩
      show ext r A v (k + (j0 + r - k)) + e₁ ≠ (k + (j0 + r - k)) * A / r + e₂
      rw [show k + (j0 + r - k) = j0 + r by omega, ext_add, gamma_shift hr0]; omega

/-- Exponent bookkeeping for T2: `(r 2^{2h+1})^J < 2^{(d-J)A'}`, `1 ≤ J < d`, `w ≤ r` and
`J w ≤ (J-1) r` give T1's arc hypothesis with `A = d A'`. -/
theorem hW_of_hJ {r A' d J w h : ℕ} (hr : 0 < r) (hw : w ≤ r) (hJ1 : 1 ≤ J) (hJd : J < d)
    (hJw : J * w ≤ (J - 1) * r)
    (hJ : (r * 2 ^ (2 * h + 1)) ^ J < 2 ^ ((d - J) * A')) :
    (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * (d * A')) < 2 ^ ((d * A' - A') * r) := by
  obtain ⟨J', rfl⟩ : ∃ J', J = J' + 1 := ⟨J - 1, by omega⟩
  obtain ⟨c, rfl⟩ : ∃ c, d = J' + 1 + c + 1 := ⟨d - J' - 2, by omega⟩
  rw [show J' + 1 + c + 1 - (J' + 1) = c + 1 by omega] at hJ
  rw [show J' + 1 - 1 = J' by omega] at hJw
  rw [show (J' + 1 + c + 1) * A' - A' = (J' + c + 1) * A' from
    Nat.sub_eq_of_eq_add (by ring)]
  apply (Nat.pow_lt_pow_iff_left (n := J' + 1) (by omega)).mp
  have hB : w * 2 ^ (2 * h + 1) ≤ r * 2 ^ (2 * h + 1) := Nat.mul_le_mul_right _ hw
  have hcw : (J' + 1) * (w - 1) ≤ J' * r := by
    have : (J' + 1) * (w - 1) ≤ (J' + 1) * w := Nat.mul_le_mul_left _ (by omega)
    omega
  calc ((w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * ((J' + 1 + c + 1) * A'))) ^ (J' + 1)
      = (w * 2 ^ (2 * h + 1)) ^ (r * (J' + 1)) *
          2 ^ ((J' + 1) * (w - 1) * ((J' + 1 + c + 1) * A')) := by
        rw [mul_pow, ← pow_mul, ← pow_mul]; congr 2; ring
    _ ≤ (r * 2 ^ (2 * h + 1)) ^ (r * (J' + 1)) * 2 ^ (J' * r * ((J' + 1 + c + 1) * A')) :=
        Nat.mul_le_mul (Nat.pow_le_pow_left hB _)
          (Nat.pow_le_pow_right (by norm_num) (Nat.mul_le_mul_right _ hcw))
    _ = ((r * 2 ^ (2 * h + 1)) ^ (J' + 1)) ^ r * 2 ^ (J' * r * ((J' + 1 + c + 1) * A')) := by
        rw [← pow_mul, mul_comm r (J' + 1)]
    _ < (2 ^ ((c + 1) * A')) ^ r * 2 ^ (J' * r * ((J' + 1 + c + 1) * A')) :=
        Nat.mul_lt_mul_of_pos_right (Nat.pow_lt_pow_left hJ (by omega)) (by positivity)
    _ = (2 ^ ((J' + c + 1) * A' * r)) ^ (J' + 1) := by
        rw [← pow_mul, ← pow_add, ← pow_mul]; congr 1; ring

/-- **T2: fewer than `d` level changes.** Let `d = gcd(A,r) ≥ 2`, `3^r + 1 < 2^A`,
`v` with entries `≥ 1` below `r`, `psum v r = A`, `v`'s partial sums not all equal to chr's.
Let the deviation `ε_j = psum v j - ⌊jA/r⌋` (partial-sum indices) satisfy `|ε_j| ≤ H`, and change
value (`ε_{m+1} ≠ ε_m`, `m < r`) only at positions in a finset `P` with `|P| < d`. If
`(r 2^{4H+1})^{|P|} < 2^{(d - |P|) A/d}`, then `(2^A - 3^r) ∤ B(v)`. The deviation may be
nonzero on an arbitrarily long stretch: only its level changes are counted. Contains every
word obtained from chr by `K` slides at arbitrary distances when `2K ≤ d - 1` (`H = K`).
Proof: free cyclic gap of length `⌊(r-1)/|P|⌋` among the jumps, a constant run `κ` of length
`≥ r/|P|`, offsets realising `κ`, and T1 on the complementary arc with `h = 2H`. -/
theorem no_cycle_few_levels_noncoprime (r A H : ℕ) (hd : 2 ≤ Nat.gcd A r)
    (hq : 3 ^ r + 1 < 2 ^ A) (v : ℕ → ℕ) (hv1 : ∀ i < r, 1 ≤ v i) (hsum : psum v r = A)
    (P : Finset ℕ) (hPd : P.card < Nat.gcd A r)
    (hJ : (r * 2 ^ (4 * H + 1)) ^ P.card < 2 ^ ((Nat.gcd A r - P.card) * (A / Nat.gcd A r)))
    (hjump : ∀ m < r, ((psum v (m + 1) : ℤ) - psum (NormGoal.chr r A) (m + 1)) ≠
        ((psum v m : ℤ) - psum (NormGoal.chr r A) m) → m ∈ P)
    (hup : ∀ j < r, psum v j ≤ psum (NormGoal.chr r A) j + H)
    (hdn : ∀ j < r, psum (NormGoal.chr r A) j ≤ psum v j + H)
    (hne : ∃ j < r, psum v j ≠ psum (NormGoal.chr r A) j) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  have hr0 : 0 < r := by obtain ⟨j, hj, -⟩ := hne; omega
  set d := Nat.gcd A r with hd_def
  set ε : ℕ → ℤ := fun j => (psum v j : ℤ) - psum (NormGoal.chr r A) j with hε
  have hε0 : ε 0 = 0 := by simp [hε, psum]
  have hεr : ε r = 0 := by
    simp only [hε]; rw [hsum, psum_chr, Nat.mul_div_cancel_left _ hr0]; simp
  set E := (range r).filter (fun m => ε (m + 1) ≠ ε m) with hEdef
  have hEr : ∀ j ∈ E, j < r := fun j hj => mem_range.mp (mem_filter.mp hj).1
  have hEP : E ⊆ P := by
    intro j hj
    obtain ⟨hj1, hj2⟩ := mem_filter.mp hj
    exact hjump j (mem_range.mp hj1) hj2
  have hnotE : ∀ m < r, m ∉ E → ε (m + 1) = ε m := by
    intro m hm hmE; by_contra hc; exact hmE (mem_filter.mpr ⟨mem_range.mpr hm, hc⟩)
  have hK1 : 0 < E.card := by
    rcases Nat.eq_zero_or_pos E.card with h0 | h0
    · exfalso
      have hE0 : E = ∅ := card_eq_zero.mp h0
      have hall : ∀ j ≤ r, ε j = 0 := by
        intro j
        induction j with
        | zero => intro _; exact hε0
        | succ j ih =>
          intro hj
          rw [hnotE j (by omega) (by rw [hE0]; simp)]; exact ih (by omega)
      obtain ⟨j, hj, hj'⟩ := hne
      have := hall j hj.le
      simp only [hε] at this; omega
    · exact h0
  set J := P.card with hJdef
  have hKJ : E.card ≤ J := card_le_card hEP
  have hJ1 : 0 < J := by omega
  set g := (r - 1) / J with hg
  have hJg : J * g < r := by
    have := Nat.mul_div_le (r - 1) J; rw [hg]; omega
  have hKg : E.card * g < r := lt_of_le_of_lt (Nat.mul_le_mul_right _ hKJ) hJg
  have hJg' : r ≤ J * (g + 1) := by
    have := Nat.lt_mul_div_succ (r - 1) hJ1; rw [hg]; omega
  have hgr : g < r := by
    have : g ≤ r - 1 := Nat.div_le_self _ _
    omega
  clear_value g
  obtain ⟨x, hx, hfree⟩ := free_gap r g E hEr hKg
  set κ := ε x with hκ
  have hrun : ∀ i ≤ g, (x + i < r → ε (x + i) = κ) ∧ (r ≤ x + i → ε (x + i - r) = κ) := by
    intro i
    induction i with
    | zero => intro _; exact ⟨fun _ => rfl, fun h => by omega⟩
    | succ i ih =>
      intro hi
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      by_cases hn : x + i < r
      · have hnE : x + i ∉ E := by
          intro hm; exact hfree _ hm (by unfold inArc; omega)
        have hstep := hnotE (x + i) hn hnE
        refine ⟨fun _ => ?_, fun h => ?_⟩
        · rw [show x + (i + 1) = x + i + 1 by omega, hstep, ih1 hn]
        · have hxi : x + i + 1 = r := by omega
          rw [show x + (i + 1) - r = 0 by omega, hε0, ← hεr, ← hxi, hstep, ih1 hn]
      · have hm : x + i - r < r := by omega
        have hnE : x + i - r ∉ E := by
          intro hm'; exact hfree _ hm' (by unfold inArc; omega)
        have hstep := hnotE (x + i - r) hm hnE
        refine ⟨fun h => by omega, fun _ => ?_⟩
        rw [show x + (i + 1) - r = x + i - r + 1 by omega, hstep, ih2 (by omega)]
  set k := if x + g + 1 < r then x + g + 1 else x + g + 1 - r with hk
  set w := r - (g + 1) with hw
  have hkr : k < r := by rw [hk]; split_ifs <;> omega
  have hcomp : ∀ j < r, ¬ inArc r k w j → ε j = κ := by
    intro j hj hj'
    have : ∃ i ≤ g, (x + i = j ∨ x + i = j + r) := by
      unfold inArc at hj'
      rw [hk] at hj'
      split_ifs at hj' with hc
      · exact ⟨j - x, by omega, by omega⟩
      · by_cases hjx : x ≤ j
        · exact ⟨j - x, by omega, by omega⟩
        · exact ⟨j + r - x, by omega, by omega⟩
    obtain ⟨i, hi, h1 | h1⟩ := this
    · have := (hrun i hi).1 (by omega); rwa [h1] at this
    · have := (hrun i hi).2 (by omega); rwa [h1, Nat.add_sub_cancel] at this
  clear_value k w
  have hκb : -(H : ℤ) ≤ κ ∧ κ ≤ H := by
    have := hup x hx; have := hdn x hx; simp only [hκ, hε]; omega
  set e₁ := (-κ).toNat with he₁
  set e₂ := κ.toNat with he₂
  have hee : (e₂ : ℤ) - e₁ = κ := by
    simp only [he₁, he₂]; omega
  have hcast : ∀ j, (psum v j + e₁ : ℤ) - (psum (NormGoal.chr r A) j + e₂) = ε j - κ := by
    intro j; simp only [hε]; omega
  obtain ⟨A'', hA''⟩ : ∃ A'', A = d * A'' := Nat.gcd_dvd_left A r
  have hAd : A / d = A'' := by rw [hA'']; exact Nat.mul_div_cancel_left _ (by omega)
  have hJw : J * w ≤ (J - 1) * r := by
    have h2 : J * w = J * r - J * (g + 1) := by rw [hw, Nat.mul_sub]
    have h3 : (J - 1) * r = J * r - r := by rw [Nat.sub_mul, one_mul]
    have h4 : r ≤ J * r := Nat.le_mul_of_pos_left r hJ1
    omega
  have hW := hW_of_hJ (A' := A'') (d := d) (h := 2 * H) hr0 (show w ≤ r by omega) hJ1 hPd hJw
    (by rw [hAd] at hJ; rw [show 2 * (2 * H) + 1 = 4 * H + 1 by ring]; exact hJ)
  refine no_cycle_offset_arc_noncoprime r A hd hq k w (2 * H) e₁ e₂ hkr (by omega)
    (by rw [hAd]; rw [hA'']; exact hW) v hv1 hsum ?_ ?_ ?_ ?_
  · intro j hj hj'
    have h1 := hcomp j hj hj'
    have h2 := hcast j
    omega
  · intro j hj
    have h1 := hcast j; have := hup j hj; have := hdn j hj
    simp only [hε] at h1; omega
  · intro j hj
    have h1 := hcast j; have := hup j hj; have := hdn j hj
    simp only [hε] at h1; omega
  · by_cases hκ0 : κ = 0
    · obtain ⟨j, hj, hj'⟩ := hne
      refine ⟨j, hj, fun heq => hj' ?_⟩
      have h1 := hcast j; simp only [hε] at h1; omega
    · refine ⟨0, hr0, fun heq => hκ0 ?_⟩
      have h1 := hcast 0; rw [hε0] at h1; omega

/-- Partial sums of a slide: `psum (slide w a b) j + [a < j] = psum w j + [b < j]`
(`a ≠ b`, `w a ≥ 1`). -/
theorem psum_slide (w : ℕ → ℕ) {a b : ℕ} (hab : a ≠ b) (ha : 1 ≤ w a) (j : ℕ) :
    psum (NormGoal.slide w a b) j + (if a < j then 1 else 0) =
      psum w j + (if b < j then 1 else 0) := by
  induction j with
  | zero => simp [psum]
  | succ j ih =>
    rw [psum_succ, psum_succ]
    by_cases hja : j = a
    · subst hja
      have hs : NormGoal.slide w j b j = w j - 1 := by simp [NormGoal.slide]
      rw [hs]
      have : ¬ j < j := lt_irrefl j
      simp only [this, ite_false, show j < j + 1 by omega, ite_true] at ih ⊢
      by_cases hb : b < j
      · simp only [hb, ite_true, show b < j + 1 by omega] at ih ⊢; omega
      · simp only [hb, ite_false, show ¬ b < j + 1 by omega] at ih ⊢; omega
    · by_cases hjb : j = b
      · subst hjb
        have hs : NormGoal.slide w a j j = w j + 1 := by simp [NormGoal.slide, Ne.symm hab]
        rw [hs]
        simp only [lt_irrefl, ite_false, show j < j + 1 by omega, ite_true] at ih ⊢
        by_cases ha' : a < j
        · simp only [ha', ite_true, show a < j + 1 by omega] at ih ⊢; omega
        · simp only [ha', ite_false, show ¬ a < j + 1 by omega] at ih ⊢; omega
      · have hs : NormGoal.slide w a b j = w j := by simp [NormGoal.slide, hja, hjb]
        rw [hs]
        have e1 : (a < j + 1) ↔ (a < j) := by omega
        have e2 : (b < j + 1) ↔ (b < j) := by omega
        simp only [e1, e2]; omega

/-- For `0 < r ≤ A` every Christoffel letter is `≥ 1`. -/
theorem chr_pos {r A : ℕ} (hr0 : 0 < r) (hAr : r ≤ A) (i : ℕ) : 1 ≤ NormGoal.chr r A i := by
  unfold NormGoal.chr
  have : i * A / r + 1 ≤ (i + 1) * A / r := by
    have : i * A / r + 1 = (i * A + r) / r := by rw [Nat.add_div_right _ hr0]
    rw [this]; apply Nat.div_le_div_right; rw [add_mul, one_mul]; omega
  omega

/-- Basic facts about `v = slide (chr r A) a b` (`a, b < r`, `a ≠ b`, `chr a ≥ 2`). -/
theorem slide_facts {r A a b : ℕ} (hq : 3 ^ r + 1 < 2 ^ A) (ha : a < r) (hb : b < r)
    (hab : a ≠ b) (h2 : 2 ≤ NormGoal.chr r A a) :
    (∀ i < r, 1 ≤ NormGoal.slide (NormGoal.chr r A) a b i) ∧
    psum (NormGoal.slide (NormGoal.chr r A) a b) r = A ∧
    (∀ j, psum (NormGoal.slide (NormGoal.chr r A) a b) j + (if a < j then 1 else 0) =
      j * A / r + (if b < j then 1 else 0)) := by
  have hr0 : 0 < r := by omega
  have hAr := r_lt_A hq
  have hps := fun j => psum_slide (NormGoal.chr r A) hab (by omega) j
  simp only [psum_chr] at hps
  refine ⟨?_, ?_, hps⟩
  · intro i _
    unfold NormGoal.slide
    have := chr_pos hr0 hAr.le i
    split_ifs with h1 h3 <;> omega
  · have := hps r
    rw [Nat.mul_div_cancel_left _ hr0] at this
    simp only [ha, hb, ite_true] at this; omega

/-- **T3a: one unit slid ANY distance, `gcd(A, r) ≥ 3`.** If `gcd(A, r) ≥ 3`,
`3^r + 1 < 2^A` and `(32 r)^6 < 2^A`, then for all `a ≠ b < r` with `chr a ≥ 2`, the word
obtained from `chr r A` by moving one unit from position `a` to position `b` does not satisfy
`(2^A - 3^r) ∣ B`. Proof: the deviation is `[b<j] - [a<j]` with level changes only at `a, b`;
T2 with `P = {a, b}`, `H = 1`. -/
theorem no_cycle_slide_noncoprime3 (r A : ℕ) (hd : 3 ≤ Nat.gcd A r) (hq : 3 ^ r + 1 < 2 ^ A)
    (h6 : (32 * r) ^ 6 < 2 ^ A) (a b : ℕ) (ha : a < r) (hb : b < r) (hab : a ≠ b)
    (h2 : 2 ≤ NormGoal.chr r A a) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r (NormGoal.slide (NormGoal.chr r A) a b) := by
  obtain ⟨hv1, hsum, hps⟩ := slide_facts hq ha hb hab h2
  have hr0 : 0 < r := by omega
  have hc : ∀ j, psum (NormGoal.chr r A) j = j * A / r := fun j => psum_chr j
  set d := Nat.gcd A r with hd_def
  obtain ⟨A'', hA''⟩ : ∃ A'', A = d * A'' := Nat.gcd_dvd_left A r
  have hAd : A / d = A'' := by rw [hA'']; exact Nat.mul_div_cancel_left _ (by omega)
  have hcard : ({a, b} : Finset ℕ).card = 2 := card_pair hab
  refine no_cycle_few_levels_noncoprime r A 1 (by omega) hq _ hv1 hsum {a, b}
    (by rw [hcard]; omega) ?_ ?_ ?_ ?_ ?_
  · rw [hcard, hAd]
    apply (Nat.pow_lt_pow_iff_left (n := 3) (by norm_num)).mp
    calc ((r * 2 ^ (4 * 1 + 1)) ^ 2) ^ 3 = (32 * r) ^ 6 := by ring
      _ < 2 ^ A := h6
      _ ≤ (2 ^ ((d - 2) * A'')) ^ 3 := by
        rw [← pow_mul, hA'']; apply Nat.pow_le_pow_right (by norm_num)
        have : d ≤ (d - 2) * 3 := by omega
        calc d * A'' ≤ (d - 2) * 3 * A'' := Nat.mul_le_mul_right _ this
          _ = (d - 2) * A'' * 3 := by ring
  · intro m hm hne
    simp only [mem_insert, mem_singleton]
    by_contra hc'
    push Not at hc'
    apply hne
    have h1 := hps (m + 1); have h0 := hps m
    rw [hc, hc]
    have e1 : (a < m + 1) ↔ (a < m) := by omega
    have e2 : (b < m + 1) ↔ (b < m) := by omega
    simp only [e1, e2] at h1
    split_ifs at h1 h0 <;> omega
  · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
  · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
  · refine ⟨max a b, by omega, ?_⟩
    have := hps (max a b); rw [hc]
    split_ifs at this <;> omega

/-- **T3b: one unit slid any distance, `gcd(A, r) ≥ 2`, explicit condition.**
Same conclusion as T3a for any `d ≥ 2`, provided the arc condition with `h = 1` holds at
`w = D = |a - b|` or at `w = r - D`. (The deviation is `∓1` on the `D` partial-sum indices
between `a` and `b` and `0` elsewhere: T1 on the first set with offset `0`, or on the second set
with offset `1`.) For `d = 2` the excluded distances leave a middle band of about 20 values
(19 at `r = 40902, A = 64832`). -/
theorem no_cycle_slide_noncoprime (r A : ℕ) (hd : 2 ≤ Nat.gcd A r) (hq : 3 ^ r + 1 < 2 ^ A)
    (a b : ℕ) (ha : a < r) (hb : b < r) (hab : a ≠ b) (h2 : 2 ≤ NormGoal.chr r A a)
    (hW : ((if a < b then b - a else a - b) * 2 ^ 3) ^ r *
            2 ^ (((if a < b then b - a else a - b) - 1) * A) <
          2 ^ ((A - A / Nat.gcd A r) * r) ∨
          ((r - (if a < b then b - a else a - b)) * 2 ^ 3) ^ r *
            2 ^ ((r - (if a < b then b - a else a - b) - 1) * A) <
          2 ^ ((A - A / Nat.gcd A r) * r)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r (NormGoal.slide (NormGoal.chr r A) a b) := by
  obtain ⟨hv1, hsum, hps⟩ := slide_facts hq ha hb hab h2
  have hr0 : 0 < r := by omega
  have hc : ∀ j, psum (NormGoal.chr r A) j = j * A / r := fun j => psum_chr j
  have hc0 : (0 : ℕ) * A / r = 0 := by simp
  have hp0 : psum (NormGoal.slide (NormGoal.chr r A) a b) 0 = 0 := by simp [psum]
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · simp only [hlt, ite_true] at hW
    rcases hW with hW | hW
    · refine no_cycle_offset_arc_noncoprime r A hd hq (a + 1) (b - a) 1 0 0 (by omega) (by omega)
        hW _ hv1 hsum ?_ ?_ ?_ ?_
      · intro j hj hj'; unfold inArc at hj'; have := hps j; rw [hc]
        split_ifs at this <;> omega
      · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
      · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
      · refine ⟨b, hb, ?_⟩; have := hps b; rw [hc]; split_ifs at this <;> omega
    · refine no_cycle_offset_arc_noncoprime r A hd hq (if b + 1 < r then b + 1 else 0)
        (r - (b - a)) 1 1 0 (by split_ifs <;> omega) (by omega) hW _ hv1 hsum ?_ ?_ ?_ ?_
      · intro j hj hj'; unfold inArc at hj'; have := hps j; rw [hc]
        split_ifs at this hj' <;> omega
      · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
      · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
      · refine ⟨0, hr0, ?_⟩; rw [hc, hc0, hp0]; omega
  · simp only [show ¬ a < b by omega, ite_false] at hW
    rcases hW with hW | hW
    · refine no_cycle_offset_arc_noncoprime r A hd hq (b + 1) (a - b) 1 0 0 (by omega) (by omega)
        hW _ hv1 hsum ?_ ?_ ?_ ?_
      · intro j hj hj'; unfold inArc at hj'; have := hps j; rw [hc]
        split_ifs at this <;> omega
      · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
      · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
      · refine ⟨a, ha, ?_⟩; have := hps a; rw [hc]; split_ifs at this <;> omega
    · refine no_cycle_offset_arc_noncoprime r A hd hq (if a + 1 < r then a + 1 else 0)
        (r - (a - b)) 1 0 1 (by split_ifs <;> omega) (by omega) hW _ hv1 hsum ?_ ?_ ?_ ?_
      · intro j hj hj'; unfold inArc at hj'; have := hps j; rw [hc]
        split_ifs at this hj' <;> omega
      · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
      · intro j _; have := hps j; rw [hc]; split_ifs at this <;> omega
      · refine ⟨0, hr0, ?_⟩; rw [hc, hc0, hp0]; omega

/-- `2^30 n^6 < 2^n` for `n ≥ 128`. -/
theorem pow6 : ∀ n, 128 ≤ n → 2 ^ 30 * n ^ 6 < 2 ^ n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    have h1 : (128 * (n + 1)) ^ 6 ≤ (129 * n) ^ 6 := Nat.pow_le_pow_left (by omega) 6
    rw [mul_pow, mul_pow] at h1
    have h2 : 128 ^ 6 * (n + 1) ^ 6 ≤ 128 ^ 6 * (2 * n ^ 6) := by
      calc 128 ^ 6 * (n + 1) ^ 6 ≤ 129 ^ 6 * n ^ 6 := h1
        _ ≤ 2 * 128 ^ 6 * n ^ 6 := Nat.mul_le_mul_right _ (by norm_num)
        _ = 128 ^ 6 * (2 * n ^ 6) := by ring
    have h3 : (n + 1) ^ 6 ≤ 2 * n ^ 6 := Nat.le_of_mul_le_mul_left h2 (by norm_num)
    calc 2 ^ 30 * (n + 1) ^ 6 ≤ 2 ^ 30 * (2 * n ^ 6) := Nat.mul_le_mul_left _ h3
      _ = 2 * (2 ^ 30 * n ^ 6) := by ring
      _ < 2 * 2 ^ n := by omega
      _ = 2 ^ (n + 1) := by ring

/-- Partial sums only read earlier letters. -/
theorem psum_congr {v u : ℕ → ℕ} {j : ℕ} (h : ∀ i < j, v i = u i) : psum v j = psum u j := by
  unfold psum; exact sum_congr rfl (fun i hi => h i (mem_range.mp hi))

/-- `B_r(v)` only reads letters below `r`. -/
theorem Bnum_congr {v u : ℕ → ℕ} {r : ℕ} (h : ∀ i < r, v i = u i) : Bnum r v = Bnum r u := by
  unfold Bnum
  apply sum_congr rfl; intro j hj
  rw [psum_congr (fun i hi => h i (by have := mem_range.mp hj; omega))]

section Cycle
open CollatzProof

/-- **Cycle form of T1.** No positive `T`-cycle with `r ≥ 2` odd steps, period `L`,
`gcd(L, r) ≥ 2`, has a valuation word whose partial sums equal `⌊jL/r⌋ + e₂ - e₁` outside a cyclic
arc `[k, k+w)` and stay within `h` of it, when the arc condition holds. -/
theorem cycle_offset_arc_noncoprime {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r)
    (hd : 2 ≤ Nat.gcd L r) (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (k w h e₁ e₂ : ℕ) (hk : k < r) (hwr : w ≤ r)
    (hW : (w * 2 ^ (2 * h + 1)) ^ r * 2 ^ ((w - 1) * L) < 2 ^ ((L - L / Nat.gcd L r) * r))
    (hout : ∀ j < r, ¬ inArc r k w j → psum v j + e₁ = psum (NormGoal.chr r L) j + e₂)
    (hup : ∀ j < r, psum v j + e₁ ≤ psum (NormGoal.chr r L) j + e₂ + h)
    (hdn : ∀ j < r, psum (NormGoal.chr r L) j + e₂ ≤ psum v j + e₁ + h)
    (hne : ∃ j < r, psum v j + e₁ ≠ psum (NormGoal.chr r L) j + e₂) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  exact no_cycle_offset_arc_noncoprime r L hd hq k w h e₁ e₂ hk hwr hW v hv1 hL hout hup hdn
    hne hdiv

/-- **Cycle form of T2.** No positive `T`-cycle with `r ≥ 2` odd steps, period `L`,
`gcd(L, r) ≥ 2`, has a valuation word whose deviation from `chr r L` is bounded by `H`, nonzero,
and changes level at fewer than `gcd(L, r)` positions `P` with
`(r 2^{4H+1})^{|P|} < 2^{(d-|P|)L/d}`. -/
theorem cycle_few_levels_noncoprime {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r)
    (hd : 2 ≤ Nat.gcd L r) (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m) (H : ℕ)
    (P : Finset ℕ) (hPd : P.card < Nat.gcd L r)
    (hJ : (r * 2 ^ (4 * H + 1)) ^ P.card < 2 ^ ((Nat.gcd L r - P.card) * (L / Nat.gcd L r)))
    (hjump : ∀ m < r, ((psum v (m + 1) : ℤ) - psum (NormGoal.chr r L) (m + 1)) ≠
        ((psum v m : ℤ) - psum (NormGoal.chr r L) m) → m ∈ P)
    (hup : ∀ j < r, psum v j ≤ psum (NormGoal.chr r L) j + H)
    (hdn : ∀ j < r, psum (NormGoal.chr r L) j ≤ psum v j + H)
    (hne : ∃ j < r, psum v j ≠ psum (NormGoal.chr r L) j) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  exact no_cycle_few_levels_noncoprime r L H hd hq v hv1 hL P hPd hJ hjump hup hdn hne hdiv

/-- **Cycle form of T3a (DIRECTIVES 2(c), non-coprime, d ≥ 3).** No nontrivial (`m ≠ 1`)
positive `T`-cycle with `r ≥ 2` odd steps and period `L`, `gcd(L, r) ≥ 3`, has as valuation word
(read from the chosen start `m`) a slide of `chr r L`: one unit moved from any position `a` to
any other position `b`. (Slides of rotations of chr: choose another start; remark only.) No size hypothesis: `r ≥ 40901` (`cycle_params`) gives `(32r)^6 < 2^L`. Non-vacuity of the
word hypotheses: `r = 122703`, `L = 194484` (`gcd = 3`, `NormArc.witness_d3`), `chr 1 = 2`,
`a = 1`, any `b`. -/
theorem cycle_slide_noncoprime3 {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hd : 3 ≤ Nat.gcd L r)
    (hm : m ≠ 1) (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (a b : ℕ) (ha : a < r) (hb : b < r) (hab : a ≠ b) (h2 : 2 ≤ NormGoal.chr r L a)
    (hv : ∀ i < r, v i = NormGoal.slide (NormGoal.chr r L) a b i) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  obtain ⟨-, hr4⟩ := NormCycleAll.cycle_params (by omega) hv1 hL hodd hcyc hm
  have hrL := r_lt_A hq
  have h6 : (32 * r) ^ 6 < 2 ^ L := by
    calc (32 * r) ^ 6 = 2 ^ 30 * r ^ 6 := by ring
      _ < 2 ^ r := pow6 r (by omega)
      _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hrL.le
  rw [Bnum_congr hv] at hdiv
  exact no_cycle_slide_noncoprime3 r L hd hq h6 a b ha hb hab h2 hdiv

/-- **Cycle form of T3b.** As T3a for `gcd(L, r) ≥ 2`, under the arc condition at `|a - b|`
or `r - |a - b|`. -/
theorem cycle_slide_noncoprime {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hd : 2 ≤ Nat.gcd L r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (a b : ℕ) (ha : a < r) (hb : b < r) (hab : a ≠ b) (h2 : 2 ≤ NormGoal.chr r L a)
    (hW : ((if a < b then b - a else a - b) * 2 ^ 3) ^ r *
            2 ^ (((if a < b then b - a else a - b) - 1) * L) <
          2 ^ ((L - L / Nat.gcd L r) * r) ∨
          ((r - (if a < b then b - a else a - b)) * 2 ^ 3) ^ r *
            2 ^ ((r - (if a < b then b - a else a - b) - 1) * L) <
          2 ^ ((L - L / Nat.gcd L r) * r))
    (hv : ∀ i < r, v i = NormGoal.slide (NormGoal.chr r L) a b i) : False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  rw [Bnum_congr hv] at hdiv
  exact no_cycle_slide_noncoprime r L hd hq a b ha hb hab h2 hW hdiv

end Cycle

end Collatz.NormPlateau

#print axioms Collatz.NormPlateau.window_core_shift
#print axioms Collatz.NormPlateau.no_cycle_offset_arc_noncoprime
#print axioms Collatz.NormPlateau.hW_of_hJ
#print axioms Collatz.NormPlateau.no_cycle_few_levels_noncoprime
#print axioms Collatz.NormPlateau.psum_slide
#print axioms Collatz.NormPlateau.no_cycle_slide_noncoprime3
#print axioms Collatz.NormPlateau.no_cycle_slide_noncoprime
#print axioms Collatz.NormPlateau.pow6
#print axioms Collatz.NormPlateau.cycle_offset_arc_noncoprime
#print axioms Collatz.NormPlateau.cycle_few_levels_noncoprime
#print axioms Collatz.NormPlateau.cycle_slide_noncoprime3
#print axioms Collatz.NormPlateau.cycle_slide_noncoprime
