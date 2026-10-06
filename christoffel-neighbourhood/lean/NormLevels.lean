import NormLebel
import NormCycleAll
import CollatzSearch.BackCong

/-!
# few level changes for every gcd, and the Terras form of the shift lift

Notation as in `NormShift`: `v` a valuation word of length `r` (letters `≥ 1`), `psum v r = A`,
`q = 2^A - 3^r`, `ε_ρ = psum v ρ - ⌊ρA/r⌋` (deviation from the Christoffel word `chr r A`),
`Pe` the partial sums of the periodic extension, `d = gcd(A, r)`, `J = |P|` a set containing all
cyclic level changes of `ε`, `g = ⌊r/((6J+3)d)⌋`.

* `gcd_window` (combinatorial core, any `d` with `r/d ≥ 2`): there is a shift `σ < r` with
  `σA = rn + t`, `1 ≤ t < r`, and a cyclic window of length `g` on which `κ = 0`
  (`quiet`). Proof: Dirichlet on `r' = r/d` for `τ = (A/d)^{-1} mod r'` with `K = 2J+1`, the
  shift `σ = s` or `s + (d-1)r'` (`|σ| < r'/(2J+1)`), `t = d t₀`, at most `d t₀` explicit
  specials `{(uτ mod r') + c r'}`, `J` change-point arcs, and the count `count_aux`.
* **T1 `few_levels_gcd`**: word-level T5 for every gcd (`NormShift` `few_levels_coprime` is `d = 1`).
* **T3 `cycle_levels_max`** (Terras form, no height, no gap/Baker input, no `r ≥ 40901`):
  for a positive `T`-cycle with MINIMAL period `L`, `r` odd steps, all elements `≤ M`,
  `d = gcd(L, r)`, `r/d ≥ 2`: if the deviation of its valuation word from `chr r L` changes
  level only in `P` and `g ≥ 2`, then `2^{g-1} < M`. Proof: the window gives
  `Pe(a+k) = n + Pe(b+k)` for `k < g` (`b = a - σ`), so the odd elements
  `T^{Pe a} m ≠ T^{Pe b} m` (minimal period) have equal parity vectors of length
  `S ≥ g - 1`, hence are congruent mod `2^S` (`modEq_of_parity`, converse of Terras 1976).
* **T2 `cycle_far_from_christoffel_rot`**: start-free cycle form of T1 for every gcd: no
  nontrivial positive `T`-cycle has a valuation word, read from ANY start `k`, with height
  `≤ H₀` deviation and `≤ J` level changes when `2^{2H₀+174} r^59 < 3^{g+1}`. Non-vacuity of the
  size hypothesis at `d = 2`: `witness_levels_gcd2` (`r = 40902`, `L = 64832`, `J = 4`).

**Honest scope / de-novelty (must accompany any flag).** At the cycle level, the `NormShift` shift-lift
and T5 are Terras 2-adic separation plus a bound on the cycle maximum: `q ∣ B(v)` gives
`G_a = 2^{Pe a} q n_a`, the lift identity says two cycle elements whose valuation words agree
on a window are 2-adically (resp. 3-adically) close, and bounded height bounds every element by
`2^{H+172} r^59`. T3 makes this explicit and Baker-free. The cycle-level content of the earlier files
is therefore "Terras + word combinatorics"; only the pure word-level divisibility forms (T1)
need the lift. T1/T2 are a routine generalization of Mghirbi's rotation-numerator lift
(Zenodo 21734655, Thm 6.3/6.4, Lemma 7.2) and `NormShift`; credit Mghirbi, Solomon (cofactor,
non-coprime), Lebel, Knight. NOT a milestone; NOT `no_nontrivial_cycles`.
-/

namespace CollatzSearch.NormLevels
open CollatzSearch.NormGoal CollatzSearch.NormReduce CollatzSearch.NormShift Finset

/-- Counting inequality for `gcd_window`: `J` arcs of length `ℓ` plus `≤ d t₀` specials leave
a free window of length `g = ⌊r/((6J+3)d)⌋`. -/
theorem count_aux {r r' d J g t0 ℓ Ec Sc : ℕ} (hrr : r = d * r') (hd0 : 0 < d)
    (hℓ : (2 * J + 1) * ℓ < r') (hgK : (6 * J + 3) * d * g ≤ r) (htK : t0 ≤ 2 * J + 1)
    (hEc : Ec ≤ d * t0) (hS : Sc ≤ J) (hg1 : 1 ≤ g) : Sc * (ℓ + g - 1) + Ec * g < r := by
  subst hrr
  have hr0 : 0 < r' := by omega
  have f1 : 3 * J * d * ((2 * J + 1) * ℓ + 1) ≤ 3 * J * d * r' := Nat.mul_le_mul_left _ hℓ
  have f2 : J * ((6 * J + 3) * d * g) ≤ J * (d * r') := Nat.mul_le_mul_left _ hgK
  have f3 : (d * t0) * ((6 * J + 3) * d * g) ≤ (d * t0) * (d * r') := Nat.mul_le_mul_left _ hgK
  have f4 : (d * t0) * (d * r') ≤ (d * (2 * J + 1)) * (d * r') :=
    Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ htK)
  have f5 : 4 * J * (d * r') * 1 ≤ 4 * J * (d * r') * d := Nat.mul_le_mul_left _ hd0
  have hpos : 0 < d * (d * r') := by positivity
  have key : (6 * J + 3) * d * (J * ℓ + J * g + (d * t0) * g) < (6 * J + 3) * d * (d * r') := by
    have e1 : (6 * J + 3) * d * (J * ℓ + J * g + d * t0 * g) + 3 * J * d =
        3 * J * d * ((2 * J + 1) * ℓ + 1) + J * ((6 * J + 3) * d * g) +
          d * t0 * ((6 * J + 3) * d * g) := by ring
    have e2 : (6 * J + 3) * d * (d * r') = 3 * J * d * r' + J * (d * r') +
        d * (2 * J + 1) * (d * r') + (4 * J * (d * r') * d - 4 * J * (d * r') * 1) +
          2 * (d * (d * r')) := by
      zify [f5]; ring
    omega
  have key' : J * ℓ + J * g + (d * t0) * g < d * r' := Nat.lt_of_mul_lt_mul_left key
  have g1 : Sc * (ℓ + g - 1) ≤ J * (ℓ + g - 1) := Nat.mul_le_mul_right _ hS
  have g2 : Ec * g ≤ (d * t0) * g := Nat.mul_le_mul_right _ hEc
  have g3 : J * (ℓ + g - 1) + J = J * ℓ + J * g := by
    rw [← mul_add_one, ← mul_add]; congr 1; omega
  omega


/-- **Window lemma, any `d = gcd(A, r)` with `r/d ≥ 2`.** If `ε` changes level
(cyclically) only in `P` and `g = ⌊r/((6|P|+3)d)⌋ ≥ 1`, there are `σ < r`, `n`, `1 ≤ t < r` with
`σA = rn + t` and a cyclic window `[x, x+g)` on which `κ` vanishes (`quiet r A t σ v`). -/
theorem gcd_window {r A d : ℕ} {v : ℕ → ℕ} (hd : Nat.gcd A r = d) (hrd : 2 ≤ r / d)
    (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, eps r A v c ≠ eps r A v (prv r c) → c ∈ P)
    (hg1 : 1 ≤ r / ((6 * P.card + 3) * d)) :
    ∃ σ n t, σ < r ∧ σ * A = r * n + t ∧ 1 ≤ t ∧ t < r ∧
      ∃ x < r, ∀ j < r, arc r x (r / ((6 * P.card + 3) * d)) j → quiet r A t σ v j := by
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.div_zero] at hrd; omega
    · exact h
  set r' := r / d with hr'
  set A' := A / d with hA'
  have hrr : r = d * r' := by rw [hr', Nat.mul_div_cancel' (hd ▸ Nat.gcd_dvd_right A r)]
  have hAA : A = d * A' := by rw [hA', Nat.mul_div_cancel' (hd ▸ Nat.gcd_dvd_left A r)]
  have hcop : Nat.Coprime A' r' := by
    have := Nat.coprime_div_gcd_div_gcd (m := A) (n := r) (by rw [hd]; omega)
    rwa [hd] at this
  have hr0 : 0 < r := by rw [hrr]; positivity
  set J := P.card with hJ
  set g := r / ((6 * J + 3) * d) with hg
  have hgK : (6 * J + 3) * d * g ≤ r := by rw [hg, mul_comm]; exact Nat.div_mul_le_self _ _
  have hgK' : (6 * J + 3) * g ≤ r' := by
    have : d * ((6 * J + 3) * g) ≤ d * r' := by rw [← hrr]; nlinarith
    exact Nat.le_of_mul_le_mul_left this hd0
  have hJr : 6 * J + 3 ≤ r' := by
    have : (6 * J + 3) * 1 ≤ (6 * J + 3) * g := Nat.mul_le_mul_left _ hg1
    omega
  obtain ⟨τ, hτr, hτ⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop (by omega)
  have hτ' : τ * A' % r' = 1 := by rw [mul_comm]; exact hτ
  obtain ⟨t0, ht1, htK, hdist⟩ := dirichlet (τ := τ) (K := 2 * J + 1) (by omega : 0 < r') (by omega)
  set s := t0 * τ % r' with hsdef
  have hsr : s < r' := Nat.mod_lt _ (by omega)
  have htr' : t0 < r' := by omega
  have hsA : s * A' % r' = t0 := by
    rw [hsdef, ← mod_mul_eq, mul_assoc, Nat.mul_mod, hτ', mul_one, Nat.mod_mod,
      Nat.mod_eq_of_lt htr']
  have e0 : s * A' = r' * (s * A' / r') + t0 := by
    have := Nat.div_add_mod (s * A') r'; rw [hsA] at this; omega
  set n0 := s * A' / r' with hn0
  set k := if s ≤ r' - s then 0 else d - 1 with hk
  set σ := s + k * r' with hσdef
  have hk1 : k ≤ d - 1 := by rw [hk]; split_ifs <;> omega
  have hkr : k * r' ≤ (d - 1) * r' := Nat.mul_le_mul_right _ hk1
  have hdr : (d - 1) * r' + r' = r := by
    rw [hrr]; conv_rhs => rw [show d = (d - 1) + 1 by omega]
    ring
  have hσr : σ < r := by omega
  have hσ : σ * A = r * (n0 + k * A') + d * t0 := by
    rw [hσdef, hrr, hAA]
    calc (s + k * r') * (d * A') = d * (s * A') + d * r' * (k * A') := by ring
      _ = _ := by rw [e0]; ring
  have hmin : min σ (r - σ) = min s (r' - s) := by
    rw [hσdef, hk]; split_ifs with h
    · simp only [zero_mul, add_zero]; omega
    · omega
  rw [← hmin] at hdist
  have htd : d * t0 ≤ d * (2 * J + 1) := Nat.mul_le_mul_left _ htK
  have htlt : d * t0 < r := by
    rw [hrr]; exact Nat.mul_lt_mul_of_pos_left (by omega) hd0
  refine ⟨σ, n0 + k * A', d * t0, hσr, hσ, Nat.le_mul_of_pos_left _ hd0 |>.trans' (by omega),
    htlt, ?_⟩
  -- specials
  set E := (range t0 ×ˢ range d).image (fun p => p.1 * τ % r' + p.2 * r') with hE
  have hEr : ∀ e ∈ E, e < r := by
    intro e he; rw [hE, mem_image] at he; obtain ⟨⟨u, c⟩, hp, rfl⟩ := he
    rw [mem_product, mem_range, mem_range] at hp
    have h1 := Nat.mod_lt (u * τ) (show 0 < r' by omega)
    have : c * r' + r' ≤ d * r' := by rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ hp.2
    simp only; omega
  have hspec : ∀ j < r, j * A % r < d * t0 → j ∈ E := by
    intro j hj hjt
    have h1 : j * A % r = d * (j * A' % r') := by
      rw [hrr, hAA, show j * (d * A') = d * (j * A') by ring, Nat.mul_mod_mul_left]
    rw [h1] at hjt
    have hu : j * A' % r' < t0 := Nat.lt_of_mul_lt_mul_left hjt
    have hjm : j % r' = (j * A' % r') * τ % r' := by
      apply mod_inj hcop (Nat.mod_lt _ (by omega)) (Nat.mod_lt _ (by omega))
      rw [← mod_mul_eq, ← mod_mul_eq, mul_assoc, Nat.mul_mod (j * A' % r'), hτ', mul_one,
        Nat.mod_mod, Nat.mod_mod]
    have hjd : j / r' < d := by
      apply Nat.div_lt_of_lt_mul; rw [mul_comm, ← hrr]; exact hj
    rw [hE, mem_image]
    refine ⟨(j * A' % r', j / r'), mem_product.mpr ⟨mem_range.mpr hu, mem_range.mpr hjd⟩, ?_⟩
    simp only
    rw [← hjm]
    have := Nat.mod_add_div j r'
    rw [mul_comm (j / r') r']; exact this
  have hEc : E.card ≤ d * t0 := by
    rw [hE]; refine card_image_le.trans ?_; rw [card_product, card_range, card_range, mul_comm]
  -- counting
  have hcount : ∀ ℓ, (2 * J + 1) * ℓ < r' → ∀ S : Finset ℕ, S.card ≤ J →
      S.card * (ℓ + g - 1) + E.card * g < r :=
    fun ℓ hℓ S hS => count_aux hrr hd0 hℓ hgK htK hEc hS hg1
  have hgr : g ≤ r := by
    have : 1 * g ≤ (6 * J + 3) * d * g := Nat.mul_le_mul_right g (by nlinarith)
    omega
  by_cases hs : σ ≤ r - σ
  · rw [min_eq_left hs] at hdist
    obtain ⟨x, hx, hfree⟩ := free_window2 (g := g) (ℓ := σ) P E (fun s hs => (hP s hs).le)
      (by omega) hEr hg1 hgr (hcount σ hdist P le_rfl)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    obtain ⟨n1, n2⟩ := hfree j hj hxj
    unfold quiet NormShift.wt
    rw [ite_eq_right_iff.mpr (fun h => absurd (hspec j hj h) n2), add_zero]
    exact cover_fwd (eps r A v) P hj hσr hchg n1
  · rw [min_eq_right (by omega)] at hdist
    set S := P.image (fun c => red2 r (c + σ)) with hS
    obtain ⟨x, hx, hfree⟩ := free_window2 (g := g) (ℓ := r - σ) S E
      (by intro s hs; rw [hS, mem_image] at hs; obtain ⟨c, hc, rfl⟩ := hs
          have := hP c hc; unfold red2; split_ifs <;> omega)
      (by omega) hEr hg1 hgr (hcount (r - σ) hdist S card_image_le)
    refine ⟨x, hx, fun j hj hxj => ?_⟩
    obtain ⟨n1, n2⟩ := hfree j hj hxj
    unfold quiet NormShift.wt
    rw [ite_eq_right_iff.mpr (fun h => absurd (hspec j hj h) n2), add_zero]
    exact cover_bwd (eps r A v) P hj hσr hchg
      (fun c hc => n1 _ (mem_image.mpr ⟨c, hc, rfl⟩))

/-- **T1: few level changes, every gcd (word level).** Let `d = gcd(A, r)`,
`r/d ≥ 2`, `3^r + 1 < 2^A`, letters `≥ 1`, `psum v r = A`, `|ε| ≤ H₀`, level changes of `ε` only
in `P`, the gap `2^A ≤ 2^172 r^58 q`, and `2^{2H₀+174} r^59 < 3^{⌊r/((6|P|+3)d)⌋+1}`. Then
`q ∤ B(v)`. `d = 1` is `NormShift.few_levels_coprime`. -/
theorem few_levels_gcd {r A H₀ d : ℕ} {v : ℕ → ℕ} (hd : Nat.gcd A r = d) (hrd : 2 ≤ r / d)
    (hq : 3 ^ r + 1 < 2 ^ A) (hv1 : ∀ i < r, 1 ≤ v i) (hA : psum v r = A)
    (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, eps r A v c ≠ eps r A v (prv r c) → c ∈ P)
    (hup : ∀ j < r, psum v j ≤ j * A / r + H₀) (hdn : ∀ j < r, j * A / r ≤ psum v j + H₀)
    (hgap : 2 ^ A ≤ 2 ^ 172 * r ^ 58 * (2 ^ A - 3 ^ r))
    (hbig : 2 ^ (2 * H₀ + 174) * r ^ 59 < 3 ^ (r / ((6 * P.card + 3) * d) + 1)) :
    ¬ (2 ^ A - 3 ^ r) ∣ Bnum r v := by
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, Nat.div_zero] at hrd; omega
    · exact h
  have hr : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h | h
    · rw [h, Nat.zero_div] at hrd; omega
    · exact h
  set g := r / ((6 * P.card + 3) * d) with hg
  have hg1 : 1 ≤ g := by
    by_contra hc
    have : g = 0 := Nat.lt_one_iff.mp (not_le.mp hc)
    rw [this, zero_add, pow_one] at hbig
    have h3 : 3 ≤ 2 ^ (2 * H₀ + 174) * r ^ 59 :=
      calc 3 ≤ 2 ^ (2 * H₀ + 174) :=
            le_trans (by norm_num : 3 ≤ 2 ^ 2) (Nat.pow_le_pow_right (by norm_num) (by omega))
        _ ≤ _ := Nat.le_mul_of_pos_right _ (by positivity)
    omega
  have hgK : (6 * P.card + 3) * d * g ≤ r := by rw [hg, mul_comm]; exact Nat.div_mul_le_self _ _
  have hgr : g < r := by
    have : 3 * g ≤ (6 * P.card + 3) * d * g := Nat.mul_le_mul_right g (by nlinarith)
    omega
  obtain ⟨σ, n, t, hσr, hσ, ht1, htr, hrun⟩ := gcd_window hd hrd P hP hchg hg1
  have hlo : ∀ j < r, j * A / r + 1 ≤ (H₀ + 1) + psum v j := fun j hj => by
    have := hdn j hj; omega
  have hhi : ∀ j < r, (H₀ + 1) + psum v j ≤ j * A / r + (2 * H₀ + 1) := fun j hj => by
    have := hup j hj; omega
  have hsz := size_ok (E := 2 * H₀ + 1) (g := g) hr (by omega) hgr hgap
    (by rw [show 173 + (2 * H₀ + 1) = 2 * H₀ + 174 by ring]; exact hbig)
  exact shift_lift (σ := σ) (t := t) (H := H₀ + 1) (E := 2 * H₀ + 1) hq hv1 hA hσr hσ ht1 htr
    hlo hhi hgr hsz hrun

section Cycle
open CollatzProof

/-- **T3: Baker-free cycle inequality (Terras route).** Let `m > 0` have
`T^L m = m` with MINIMAL period `L`, odd steps at the partial sums of `v` (`r` odd steps), all
orbit elements `≤ M`, `d = gcd(L, r)` with `r/d ≥ 2`. If the deviation of `v` from `chr r L`
changes level (cyclically) only at the points of `P` and `g = ⌊r/((6|P|+3)d)⌋ ≥ 2`, then
`2^{g-1} < M`. No height bound, no `3^r < 2^L`, no gap/Baker input, no `r ≥ 40901`.
Equivalently, `|P| ≥ (r/(d(log₂ M + 1)) - 3)/6`. Content: Terras 1976 (equal parity vectors of
length `S` ⇔ congruence mod `2^S`) plus the word combinatorics of `gcd_window`. -/
theorem cycle_levels_max {m L r M : ℕ} {v : ℕ → ℕ} (hr : 1 ≤ r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hprim : ∀ e, 0 < e → e < L → T^[e] m ≠ m)
    (hM : ∀ j < L, T^[j] m ≤ M)
    (hrd : 2 ≤ r / Nat.gcd L r)
    (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, eps r L v c ≠ eps r L v (prv r c) → c ∈ P)
    (hg : 2 ≤ r / ((6 * P.card + 3) * Nat.gcd L r)) :
    2 ^ (r / ((6 * P.card + 3) * Nat.gcd L r) - 1) < M := by
  have hr0 : 0 < r := by omega
  obtain ⟨σ, n, t, hσr, hσ, ht1, htr, x, hx, hxrun⟩ :=
    gcd_window (v := v) rfl hrd P hP hchg (by omega)
  set g := r / ((6 * P.card + 3) * Nat.gcd L r) with hgdef
  have hgr : g ≤ r := Nat.div_le_self _ _
  have hσ1 : 1 ≤ σ := by
    rcases Nat.eq_zero_or_pos σ with h | h
    · rw [h, zero_mul] at hσ; omega
    · exact h
  -- strict monotonicity of `Pe`
  have hlt : ∀ i j, i < j → Pe r v i < Pe r v j := by
    intro i j hij
    have := Pe_mono hr0 hv1 i (j - i); rw [Nat.add_sub_cancel' hij.le] at this; omega
  have hlt' : ∀ i j, Pe r v i < Pe r v j → i < j := by
    intro i j h; by_contra hc; push Not at hc
    rcases hc.lt_or_eq with h' | h'
    · have := hlt _ _ h'; omega
    · subst h'; omega
  have hL0 : 0 < L := by
    have := hlt 0 r hr0; rwa [Pe_zero, Pe_of_le v le_rfl, hL] at this
  -- agreement of the periodic partial sums on the window
  have hZ := fun i (hi : σ ≤ i) => Z_iff (v := v) hr0 hL hσr hσ htr hi
  have hrun' : ∀ k < g, Pe r v (x + r + k) = n + Pe r v (x + r + k - σ) := by
    intro k hk
    rw [hZ _ (by omega)]
    have hm : (x + r + k) % r = if r ≤ x + k then x + k - r else x + k := by
      rw [show x + r + k = (x + k) + r by ring, Nat.add_mod_right]; exact mod_lt_two (by omega)
    rw [hm]
    apply hxrun
    · split_ifs <;> omega
    · unfold arc; split_ifs <;> omega
  have hstar : ∀ k < g, Pe r v (x + r + k) = n + Pe r v (x + r - σ + k) := by
    intro k hk; have := hrun' k hk; rwa [show x + r + k - σ = x + r - σ + k by omega] at this
  set a := x + r with ha
  set b := a - σ with hb
  have hba : b + σ = a := by omega
  -- odd positions of the periodic orbit
  have hper : Function.IsPeriodicPt T L m := hcyc
  have hred : ∀ N, T^[N] m = T^[N % L] m := fun N => (hper.iterate_mod_apply N).symm
  have hoddN : ∀ N, T^[N] m % 2 = 1 ↔ ∃ i, Pe r v i = N := by
    intro N
    rw [hred N, hodd _ (Nat.mod_lt _ hL0)]
    constructor
    · rintro ⟨i, hi, hpi⟩
      refine ⟨i + r * (N / L), ?_⟩
      rw [Pe_add_mul hL, Pe_of_le v hi.le, hpi]; exact Nat.mod_add_div N L
    · rintro ⟨i, rfl⟩
      refine ⟨i % r, Nat.mod_lt _ hr0, ?_⟩
      have h1 := Pe_mod hr0 hL i
      have h2 : psum v (i % r) < L := by
        have := hlt (i % r) r (Nat.mod_lt _ hr0)
        rwa [Pe_of_le v (Nat.mod_lt _ hr0).le, Pe_of_le v le_rfl, hL] at this
      rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h2]
  -- equal parity vectors of length `S`
  set S := Pe r v (a + (g - 1)) - Pe r v a with hSdef
  have hSg : g - 1 ≤ S := by have := Pe_mono hr0 hv1 a (g - 1); omega
  have h0 := hstar 0 (by omega)
  have hg1 := hstar (g - 1) (by omega)
  simp only [add_zero] at h0
  have hSb : Pe r v (b + (g - 1)) = Pe r v b + S := by omega
  have hkey : ∀ s < S, ((∃ i, Pe r v i = s + Pe r v a) ↔ (∃ i, Pe r v i = s + Pe r v b)) := by
    intro s hs
    constructor
    · rintro ⟨i, hi⟩
      have hai : a ≤ i := by
        by_contra hc; have := hlt i a (by omega); omega
      have hia : i < a + (g - 1) := hlt' _ _ (by omega)
      have := hstar (i - a) (by omega)
      rw [show a + (i - a) = i by omega] at this
      exact ⟨b + (i - a), by omega⟩
    · rintro ⟨i, hi⟩
      have hbi : b ≤ i := by
        by_contra hc; have := hlt i b (by omega); omega
      have hib : i < b + (g - 1) := hlt' _ _ (by omega)
      have := hstar (i - b) (by omega)
      rw [show b + (i - b) = i by omega] at this
      exact ⟨a + (i - b), by omega⟩
  set y1 := T^[Pe r v a] m with hy1
  set y2 := T^[Pe r v b] m with hy2
  have hpar : ∀ s < S, T^[s] y1 % 2 = T^[s] y2 % 2 := by
    intro s hs
    rw [hy1, hy2, ← Function.iterate_add_apply, ← Function.iterate_add_apply]
    have e1 := hoddN (s + Pe r v a)
    have e2 := hoddN (s + Pe r v b)
    have := hkey s hs
    by_cases hA : T^[s + Pe r v a] m % 2 = 1
    · have : T^[s + Pe r v b] m % 2 = 1 := e2.mpr (this.mp (e1.mp hA))
      omega
    · have : ¬ T^[s + Pe r v b] m % 2 = 1 := fun h' => hA (e1.mpr (this.mpr (e2.mp h')))
      omega
  have hcong : y1 ≡ y2 [MOD 2 ^ S] := modEq_of_parity S hpar
  -- the two points are distinct (minimal period)
  have hab : Pe r v b < Pe r v a := hlt b a (by omega)
  have haL : Pe r v a < Pe r v b + L := by
    have h1 := hlt a (b + r) (by omega); have h2 := Pe_add hL b; omega
  have hne : y1 ≠ y2 := by
    intro h
    set c := L - Pe r v b % L with hc
    have hcz : (c + Pe r v b) % L = 0 := by
      have e : c + Pe r v b = L * (Pe r v b / L + 1) := by
        have := Nat.div_add_mod (Pe r v b) L; have := Nat.mod_lt (Pe r v b) hL0
        rw [mul_add, mul_one]; omega
      rw [e, Nat.mul_mod_right]
    have hcm : T^[c + Pe r v b] m = m := by rw [hred, hcz]; rfl
    have : T^[Pe r v a - Pe r v b] m = m := by
      conv_lhs => rw [← hcm]
      rw [← Function.iterate_add_apply,
        show Pe r v a - Pe r v b + (c + Pe r v b) = c + Pe r v a by omega,
        Function.iterate_add_apply, ← hy1, h, hy2, ← Function.iterate_add_apply, hcm]
    exact hprim _ (by omega) (by omega) this
  -- sizes
  have hy1M : y1 ≤ M := by rw [hy1, hred]; exact hM _ (Nat.mod_lt _ hL0)
  have hy2M : y2 ≤ M := by rw [hy2, hred]; exact hM _ (Nat.mod_lt _ hL0)
  have hy1o : y1 % 2 = 1 := (hoddN _).mpr ⟨a, rfl⟩
  have hy2o : y2 % 2 = 1 := (hoddN _).mpr ⟨b, rfl⟩
  have hpow : 2 ^ (g - 1) ≤ 2 ^ S := Nat.pow_le_pow_right (by norm_num) hSg
  have hpos : 0 < 2 ^ S := by positivity
  rcases lt_or_gt_of_ne hne with h | h
  · have hd : 2 ^ S ∣ y2 - y1 := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hcong.symm)
    have := Nat.le_of_dvd (by omega) hd
    omega
  · have hd : 2 ^ S ∣ y1 - y2 := Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq hcong)
    have := Nat.le_of_dvd (by omega) hd
    omega

/-- **T2: start-free cycle form of T1, every gcd.** No nontrivial (`m ≠ 1`)
positive `T`-cycle with `r ≥ 2` odd steps and period `L` has a valuation word, read from ANY
start `k` (`rot r k v`), whose deviation from `chr r L` has height `≤ H₀` and changes level only
in `P`, when `2^{2H₀+174} r^59 < 3^{⌊r/((6|P|+3)gcd(L,r))⌋+1}`. (`cycle_params`: `r < L < 2r`, so
`r ∤ L` and `r/gcd ≥ 2`; rotation by `dvd_Bnum_rot`; gap by `gap_all59`.) -/
theorem cycle_far_from_christoffel_rot {m L r k H₀ : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r) (hm : m ≠ 1)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (P : Finset ℕ) (hP : ∀ c ∈ P, c < r)
    (hchg : ∀ c < r, eps r L (NormLebel.rot r k v) c ≠
        eps r L (NormLebel.rot r k v) (prv r c) → c ∈ P)
    (hup : ∀ j < r, psum (NormLebel.rot r k v) j ≤ j * L / r + H₀)
    (hdn : ∀ j < r, j * L / r ≤ psum (NormLebel.rot r k v) j + H₀)
    (hbig : 2 ^ (2 * H₀ + 174) * r ^ 59 < 3 ^ (r / ((6 * P.card + 3) * Nat.gcd L r) + 1)) :
    False := by
  obtain ⟨hq, hdiv⟩ := NormTwo.cycle_q hr hv1 hL hodd hcyc
  obtain ⟨hL2, -⟩ := NormCycleAll.cycle_params (by omega) hv1 hL hodd hcyc hm
  have hrL : r < L := by
    by_contra hc; push Not at hc
    have h1 : 2 ^ L ≤ 2 ^ r := Nat.pow_le_pow_right (by norm_num) hc
    have h2 : 2 ^ r ≤ 3 ^ r := Nat.pow_le_pow_left (by norm_num) r
    omega
  -- `r / gcd(L, r) ≥ 2`
  have hrd : 2 ≤ r / Nat.gcd L r := by
    obtain ⟨c, hc⟩ := Nat.gcd_dvd_right L r
    have hd0 : 0 < Nat.gcd L r := Nat.gcd_pos_of_pos_right _ (by omega)
    have hrc : r / Nat.gcd L r = c := by
      set d := Nat.gcd L r
      rw [hc]; exact Nat.mul_div_cancel_left c hd0
    rw [hrc]
    by_contra hc2; push Not at hc2
    interval_cases c
    · omega
    · rw [mul_one] at hc
      obtain ⟨e, he⟩ := Nat.gcd_dvd_left L r
      rw [← hc] at he
      rcases Nat.lt_or_ge e 2 with h | h
      · interval_cases e <;> omega
      · have : r * 2 ≤ r * e := Nat.mul_le_mul_left _ h
        omega
  -- rotate
  have hrot1 : ∀ i < r, 1 ≤ NormLebel.rot r k v i := fun i _ => hv1 _ (Nat.mod_lt _ (by omega))
  have hrotL : psum (NormLebel.rot r k v) r = L := by
    have h1 := NormLebel.Pe_rot (r := r) (k := k) (v := v) r
    have h2 := Pe_add hL k
    omega
  have hdiv' : (2 ^ L - 3 ^ r) ∣ Bnum r (NormLebel.rot r k v) :=
    (NormLebel.dvd_Bnum_rot (k := k) (by omega) hq dvd_rfl hL).mpr hdiv
  exact few_levels_gcd rfl hrd hq hrot1 hrotL P hP hchg hup hdn
    (gap_all59 (by omega) (by omega)) hbig hdiv'

end Cycle

/-- Numerical instance (`d = 2`): `gcd(64832, 40902) = 2`, `H₀ = 1`, `J = 4`,
`g = ⌊40902/54⌋ = 757`. -/
theorem witness_levels_gcd2 : Nat.gcd 64832 40902 = 2 ∧
    2 ^ (2 * 1 + 174) * 40902 ^ 59 < 3 ^ (40902 / ((6 * 4 + 3) * 2) + 1) := by
  refine ⟨by decide +kernel, by decide +kernel⟩

end CollatzSearch.NormLevels

#print axioms CollatzSearch.NormLevels.count_aux
#print axioms CollatzSearch.NormLevels.gcd_window
#print axioms CollatzSearch.NormLevels.few_levels_gcd
#print axioms CollatzSearch.NormLevels.cycle_levels_max
#print axioms CollatzSearch.NormLevels.cycle_far_from_christoffel_rot
#print axioms CollatzSearch.NormLevels.witness_levels_gcd2

