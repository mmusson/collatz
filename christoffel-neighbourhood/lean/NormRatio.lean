import NormFold

/-!
# the `NormFold` self-fold as a cycle-level periodic-or-far-from-periodic dichotomy

Notation: `P_i = psum v i`, `y_i = T^{P_i}(m)` (the odd points of the cycle),
`B_i = Bnum i v`, `r = (n+1) r'`, `L = (n+1) A'`.

* `prefix_eq` (T0): `2^{P_i} y_i = 3^i m + B_i` for `i ≤ r` (prefix form of the Böhm–Sontacchi
  equation); `Bnum_grow` (T0'): `3^d B_i ≤ B_{i+d}`; `window_bound`: `3^{j-i} y_i ≤ 2^{P_j-P_i} y_j`.
* `cycle_balanced` (T1): if the odd points lie in `[m0, M]` and `2^L M ≤ 2^h 3^r m0`, the word
  is two-sided `h`-balanced on every window (`|(j-i)L - r(P_j - P_i)| ≤ r h`);
  `cycle_balanced_fold`: the scaled form, exactly `NormFold`'s `hbal`.
* `periodic_cycle_shorter` (T2): an `r'`-periodic cycle word (no bad columns) forces
  `T^{A'} m = m` (sign propagation in `2^{A'} z_{t+1} = 3^{r'} z_t + B_{r'}`).
* `cycle_fold_ratio` (T3, main): a primitive positive `T`-cycle with `p = n+1 ∣ gcd(r, L)` and
  `2^L M ≤ 2^h 3^r m0` has at least `r'/g` non-`r'`-periodic columns whenever
  `(n r' 2^{2h+1})^2 < 2^{3(g+1)}`; `cycle_periodic_or_far`: the explicit dichotomy without
  primitivity; `cycle_fold_ratio'`: convenience form (`2^L ≤ 2·3^r`, `M ≤ 2^{h-1} m0`);
  `witness_ratio`: `r = 40902`, `L = 64832`, `h = 5`, `g = 16` gives `≥ 1279` bad columns.
* `fold_count_nonvacuous` (T4): the word `(1,3,2,…,2)` (`r' = 7`, `A' = 14`, `h = 1`, `g = 3`)
  satisfies every hypothesis of `NormFold.no_cycle_fold_count` (kernel-checked).

Scope: a corollary of `NormFold` plus two elementary lemmas. T1 is classical in spirit
(Halbeisen–Hungerbühler, Eliahou-type window estimates); T2 is elementary. No unconditional
bound `M/m0 = O(r^c)` is known, so T3 stays conditional on the max/min ratio.
Prior art: Solomon (cofactor `S_d`), Knight, Lebel, Mghirbi.
-/

namespace Collatz.NormRatio
open Collatz.NormGoal Collatz.NormFold Collatz.NormBridge CollatzProof Finset

/-- **T0 (prefix equation).** Under the cycle-word hypotheses, for `i ≤ r`:
`2^{P_i} · T^{P_i}(m) = 3^i m + B_i(v)`. -/
theorem prefix_eq {m L r : ℕ} {v : ℕ → ℕ} (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) :
    ∀ i ≤ r, 2 ^ psum v i * T^[psum v i] m = 3 ^ i * m + Bnum i v := by
  have claim : ∀ i ≤ r, oddSteps (psum v i) m = i ∧ bsum (psum v i) m = Bnum i v := by
    intro i
    induction i with
    | zero => intro _; simp [psum, oddSteps, bsum, Bnum]
    | succ i ih =>
      intro hi
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hvi := hv1 i (by omega)
      have hLi : psum v (i + 1) ≤ L := hL ▸ psum_mono v hi
      rw [psum_succ] at hLi
      have inner : ∀ s, 1 ≤ s → s ≤ v i →
          oddSteps (psum v i + s) m = i + 1 ∧ bsum (psum v i + s) m = Bnum (i + 1) v := by
        intro s hs1 hs2
        induction s with
        | zero => omega
        | succ s ihs =>
          rcases Nat.eq_zero_or_pos s with h0 | hpos
          · subst h0
            have hodd1 : T^[psum v i] m % 2 = 1 :=
              (hodd (psum v i) (by omega)).mpr ⟨i, by omega, rfl⟩
            rw [← add_assoc, add_zero, oddSteps_succ_last, Bnum_succ]
            simp only [bsum, hodd1, ite_true]
            rw [ih1, ih2]; exact ⟨rfl, rfl⟩
          · obtain ⟨e1, e2⟩ := ihs hpos (by omega)
            have heven : T^[psum v i + s] m % 2 = 0 := by
              have : ¬ T^[psum v i + s] m % 2 = 1 := by
                rw [hodd _ (by omega)]
                rintro ⟨i', hi', heq⟩
                rcases Nat.lt_or_ge i i' with h | h
                · have := psum_mono v (show i + 1 ≤ i' by omega)
                  rw [psum_succ] at this; omega
                · have := psum_mono v h; omega
              omega
            rw [← add_assoc, oddSteps_succ_last, heven, add_zero]
            simp only [bsum, heven, zero_ne_one, ite_false]
            exact ⟨e1, e2⟩
      rw [psum_succ]
      exact inner (v i) hvi le_rfl
  intro i hi
  obtain ⟨c1, c2⟩ := claim i hi
  rw [bsum_affine, c1, c2]

/-- **T0' (growth of the numerator).** `3^d · B_i(v) ≤ B_{i+d}(v)`. -/
theorem Bnum_grow (v : ℕ → ℕ) (i : ℕ) : ∀ d, 3 ^ d * Bnum i v ≤ Bnum (i + d) v := by
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    rw [← add_assoc, Bnum_succ, pow_succ]
    calc 3 ^ d * 3 * Bnum i v = 3 * (3 ^ d * Bnum i v) := by ring
      _ ≤ 3 * Bnum (i + d) v := Nat.mul_le_mul_left _ ih
      _ ≤ _ := Nat.le_add_right _ _

/-- **Window bound.** For `i ≤ j ≤ r`, with `y_i = T^{P_i}(m)`:
`3^{j-i} y_i ≤ 2^{P_j - P_i} y_j`. -/
theorem window_bound {m L r : ℕ} {v : ℕ → ℕ} (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) {i j : ℕ} (hij : i ≤ j)
    (hj : j ≤ r) :
    3 ^ (j - i) * T^[psum v i] m ≤ 2 ^ (psum v j - psum v i) * T^[psum v j] m := by
  have ei := prefix_eq hv1 hL hodd i (by omega)
  have ej := prefix_eq hv1 hL hodd j hj
  have hg := Bnum_grow v i (j - i)
  rw [show i + (j - i) = j by omega] at hg
  have hP := psum_mono v hij
  have h2 : 2 ^ psum v j = 2 ^ psum v i * 2 ^ (psum v j - psum v i) := by
    rw [← pow_add]; congr 1; omega
  have h3 : 3 ^ j = 3 ^ (j - i) * 3 ^ i := by rw [← pow_add]; congr 1; omega
  have key : 2 ^ psum v i * (3 ^ (j - i) * T^[psum v i] m) ≤
      2 ^ psum v i * (2 ^ (psum v j - psum v i) * T^[psum v j] m) := by
    calc 2 ^ psum v i * (3 ^ (j - i) * T^[psum v i] m)
        = 3 ^ (j - i) * (2 ^ psum v i * T^[psum v i] m) := by ring
      _ = 3 ^ (j - i) * (3 ^ i * m) + 3 ^ (j - i) * Bnum i v := by rw [ei]; ring
      _ ≤ 3 ^ j * m + Bnum j v := by rw [h3]; nlinarith
      _ = 2 ^ psum v i * (2 ^ (psum v j - psum v i) * T^[psum v j] m) := by
        rw [← ej, h2]; ring
  exact Nat.le_of_mul_le_mul_left key (by positivity)


/-- Exponent comparison from a product inequality: `2^a · X ≤ 2^b · X`, `X > 0` ⇒ `a ≤ b`. -/
theorem exp_le_of {a b X : ℕ} (hX : 0 < X) (h : 2 ^ a * X ≤ 2 ^ b * X) : a ≤ b :=
  (Nat.pow_le_pow_iff_right (by norm_num)).mp (Nat.le_of_mul_le_mul_right h hX)

/-- **T1 (max/min ratio ⇒ two-sided balance).** Let a positive `T`-cycle of length `L` with `r`
odd steps have valuation word `v` and odd points `y_i = T^{P_i}(m)` in `[m0, M]`, with
`3^r ≤ 2^L` and `2^L M ≤ 2^h 3^r m0`. Then every window `[i, j]` (`i ≤ j ≤ r`) is two-sided
`h`-balanced: `(j-i) L ≤ r S + r h` and `r S ≤ (j-i) L + r h`, where `S = P_j - P_i`. -/
theorem cycle_balanced {m L r h m0 M : ℕ} {v : ℕ → ℕ} (hm : 0 < m) (hm0 : 0 < m0)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hlo : ∀ i < r, m0 ≤ T^[psum v i] m) (hhi : ∀ i < r, T^[psum v i] m ≤ M)
    (h3 : 3 ^ r ≤ 2 ^ L) (hR : 2 ^ L * M ≤ 2 ^ h * 3 ^ r * m0) :
    ∀ i j, i ≤ j → j ≤ r →
      (j - i) * L ≤ r * (psum v j - psum v i) + r * h ∧
      r * (psum v j - psum v i) ≤ (j - i) * L + r * h := by
  intro i j hij hj
  rcases Nat.eq_zero_or_pos r with hr0 | hr0
  · subst hr0; have : j = 0 := by omega
    subst this; have : i = 0 := by omega
    subst this; simp
  have hp0 : psum v 0 = 0 := by simp [psum]
  have hy0 : T^[psum v 0] m = m := by rw [hp0]; rfl
  have hyr : T^[psum v r] m = m := by rw [hL, hcyc]
  -- bounds for all indices ≤ r
  have hlo' : ∀ i ≤ r, m0 ≤ T^[psum v i] m := by
    intro i hi
    rcases Nat.lt_or_ge i r with h | h
    · exact hlo i h
    · have : i = r := by omega
      subst this; rw [hyr]; have := hlo 0 hr0; rwa [hy0] at this
  have hhi' : ∀ i ≤ r, T^[psum v i] m ≤ M := by
    intro i hi
    rcases Nat.lt_or_ge i r with h | h
    · exact hhi i h
    · have : i = r := by omega
      subst this; rw [hyr]; have := hhi 0 hr0; rwa [hy0] at this
  have hm0M : m0 ≤ M := (hlo' 0 (by omega)).trans (hhi' 0 (by omega))
  have hMpos : 0 < M := by omega
  -- M ≤ 2^h m0
  have hH : M ≤ 2 ^ h * m0 := by
    have : 2 ^ L * M ≤ 2 ^ L * (2 ^ h * m0) := by
      calc 2 ^ L * M ≤ 2 ^ h * 3 ^ r * m0 := hR
        _ ≤ 2 ^ h * 2 ^ L * m0 := by gcongr
        _ = 2 ^ L * (2 ^ h * m0) := by ring
    exact Nat.le_of_mul_le_mul_left this (by positivity)
  set yi := T^[psum v i] m with hyi
  set yj := T^[psum v j] m with hyj
  set S := psum v j - psum v i with hS
  set k := j - i with hk
  have hPij := psum_mono v hij
  have hPj : psum v j ≤ L := hL ▸ psum_mono v hj
  obtain ⟨c, hc⟩ : ∃ c, r = k + c := ⟨r - k, by omega⟩
  -- (a) 3^k m0 ≤ 2^S M
  have hW := window_bound hv1 hL hodd hij hj
  rw [← hyi, ← hyj] at hW
  have ha : 3 ^ k * m0 ≤ 2 ^ S * M :=
    calc 3 ^ k * m0 ≤ 3 ^ k * yi := Nat.mul_le_mul_left _ (hlo' i (by omega))
      _ ≤ 2 ^ S * yj := hW
      _ ≤ 2 ^ S * M := Nat.mul_le_mul_left _ (hhi' j hj)
  -- (b) 3^c 2^S m0 ≤ 2^L M
  have hW1 := window_bound hv1 hL hodd (Nat.zero_le i) (by omega : i ≤ r)
  rw [hy0, hp0, Nat.sub_zero, Nat.sub_zero, ← hyi] at hW1
  have hW2 := window_bound hv1 hL hodd hj le_rfl
  rw [hyr, hL, ← hyj] at hW2
  have hb0 : 3 ^ c * 2 ^ S * yj ≤ 2 ^ L * yi := by
    have hprod := Nat.mul_le_mul hW1 hW2
    have e3 : 3 ^ c = 3 ^ i * 3 ^ (r - j) := by rw [← pow_add]; congr 1; omega
    have e2 : 2 ^ L = 2 ^ psum v i * 2 ^ (L - psum v j) * 2 ^ S := by
      rw [← pow_add, ← pow_add]; congr 1; omega
    have : m * (3 ^ c * 2 ^ S * yj) ≤ m * (2 ^ L * yi) := by
      calc m * (3 ^ c * 2 ^ S * yj) = 2 ^ S * (3 ^ i * m * (3 ^ (r - j) * yj)) := by
            rw [e3]; ring
        _ ≤ 2 ^ S * (2 ^ psum v i * yi * (2 ^ (L - psum v j) * m)) :=
            Nat.mul_le_mul_left _ hprod
        _ = m * (2 ^ L * yi) := by rw [e2]; ring
    exact Nat.le_of_mul_le_mul_left this hm
  have hb : 3 ^ c * 2 ^ S * m0 ≤ 2 ^ L * M :=
    calc 3 ^ c * 2 ^ S * m0 ≤ 3 ^ c * 2 ^ S * yj := Nat.mul_le_mul_left _ (hlo' j hj)
      _ ≤ 2 ^ L * yi := hb0
      _ ≤ 2 ^ L * M := Nat.mul_le_mul_left _ (hhi' i (by omega))
  constructor
  · -- kL ≤ rS + rh
    have P1 := Nat.pow_le_pow_left ha r
    have P2 := Nat.pow_le_pow_left hR k
    have P3 := Nat.pow_le_pow_left hH c
    have P := Nat.mul_le_mul (Nat.mul_le_mul P1 P2) P3
    have hX : 0 < 3 ^ (k * r) * m0 ^ r * M ^ r := by positivity
    apply exp_le_of hX
    calc 2 ^ (k * L) * (3 ^ (k * r) * m0 ^ r * M ^ r)
        = (3 ^ k * m0) ^ r * (2 ^ L * M) ^ k * M ^ c := by
          rw [hc]; simp only [mul_pow, ← pow_mul, pow_add]; ring
      _ ≤ (2 ^ S * M) ^ r * (2 ^ h * 3 ^ r * m0) ^ k * (2 ^ h * m0) ^ c := P
      _ = 2 ^ (r * S + r * h) * (3 ^ (k * r) * m0 ^ r * M ^ r) := by
          rw [hc]; simp only [mul_pow, ← pow_mul, pow_add]; ring
  · -- rS ≤ kL + rh
    have P1 := Nat.pow_le_pow_left hb r
    have P2 := Nat.pow_le_pow_left hR c
    have P3 := Nat.pow_le_pow_left hH k
    have P := Nat.mul_le_mul (Nat.mul_le_mul P1 P2) P3
    have hY : 0 < 3 ^ (c * r) * m0 ^ r * M ^ r := by positivity
    have : r * S + L * c ≤ (k * L + r * h) + L * c := by
      apply exp_le_of hY
      calc 2 ^ (r * S + L * c) * (3 ^ (c * r) * m0 ^ r * M ^ r)
          = (3 ^ c * 2 ^ S * m0) ^ r * (2 ^ L * M) ^ c * M ^ k := by
            rw [hc]; simp only [mul_pow, ← pow_mul, pow_add]; ring
        _ ≤ (2 ^ L * M) ^ r * (2 ^ h * 3 ^ r * m0) ^ c * (2 ^ h * m0) ^ k := P
        _ = 2 ^ (k * L + r * h + L * c) * (3 ^ (c * r) * m0 ^ r * M ^ r) := by
            rw [hc]; simp only [mul_pow, ← pow_mul, pow_add]; ring
    omega

/-- **Scaled T1.** With `r = (n+1) r'` and `L = (n+1) A'`, the T1 conclusion is exactly the
balance hypothesis `hbal` of `NormFold.no_cycle_fold_count`. -/
theorem cycle_balanced_fold {m n r' A' h m0 M : ℕ} {v : ℕ → ℕ} (hm : 0 < m) (hm0 : 0 < m0)
    (hv1 : ∀ i < (n + 1) * r', 1 ≤ v i) (hL : psum v ((n + 1) * r') = (n + 1) * A')
    (hodd : ∀ j < (n + 1) * A', (T^[j] m % 2 = 1 ↔ ∃ i < (n + 1) * r', psum v i = j))
    (hcyc : T^[(n + 1) * A'] m = m)
    (hlo : ∀ i < (n + 1) * r', m0 ≤ T^[psum v i] m)
    (hhi : ∀ i < (n + 1) * r', T^[psum v i] m ≤ M)
    (h3 : 3 ^ ((n + 1) * r') ≤ 2 ^ ((n + 1) * A'))
    (hR : 2 ^ ((n + 1) * A') * M ≤ 2 ^ h * 3 ^ ((n + 1) * r') * m0) :
    ∀ i j, i ≤ j → j ≤ (n + 1) * r' →
      (j - i) * A' ≤ r' * (psum v j - psum v i) + r' * h ∧
      r' * (psum v j - psum v i) ≤ (j - i) * A' + r' * h := by
  intro i j hij hj
  obtain ⟨H1, H2⟩ := cycle_balanced hm hm0 hv1 hL hodd hcyc hlo hhi h3 hR i j hij hj
  generalize j - i = k at H1 H2 ⊢
  generalize psum v j - psum v i = S at H1 H2 ⊢
  constructor
  · refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos n)
    calc (n + 1) * (k * A') = k * ((n + 1) * A') := by ring
      _ ≤ (n + 1) * r' * S + (n + 1) * r' * h := H1
      _ = (n + 1) * (r' * S + r' * h) := by ring
  · refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos n)
    calc (n + 1) * (r' * S) = (n + 1) * r' * S := by ring
      _ ≤ k * ((n + 1) * A') + (n + 1) * r' * h := H2
      _ = (n + 1) * (k * A' + r' * h) := by ring

/-- Rigidity of the affine recursion `U z_{t+1} = V z_t + B` (increasing case). -/
theorem chain_lt {z : ℕ → ℕ} {U V B n : ℕ} (hV : 0 < V)
    (hE : ∀ t ≤ n, U * z (t + 1) = V * z t + B) (h01 : z 0 < z 1) : ∀ t ≤ n, z t < z (t + 1) := by
  intro t
  induction t with
  | zero => intro _; exact h01
  | succ t ih =>
    intro ht
    have a := ih (by omega)
    have e1 := hE t (by omega)
    have e2 := hE (t + 1) ht
    have : U * z (t + 1) < U * z (t + 1 + 1) := by
      rw [e1, e2]; have := Nat.mul_lt_mul_of_pos_left a hV; omega
    exact Nat.lt_of_mul_lt_mul_left this

/-- Rigidity of the affine recursion `U z_{t+1} = V z_t + B` (decreasing case). -/
theorem chain_gt {z : ℕ → ℕ} {U V B n : ℕ} (hV : 0 < V)
    (hE : ∀ t ≤ n, U * z (t + 1) = V * z t + B) (h01 : z 1 < z 0) : ∀ t ≤ n, z (t + 1) < z t := by
  intro t
  induction t with
  | zero => intro _; exact h01
  | succ t ih =>
    intro ht
    have a := ih (by omega)
    have e1 := hE t (by omega)
    have e2 := hE (t + 1) ht
    have : U * z (t + 1 + 1) < U * z (t + 1) := by
      rw [e1, e2]; have := Nat.mul_lt_mul_of_pos_left a hV; omega
    exact Nat.lt_of_mul_lt_mul_left this

/-- If `U z_{t+1} = V z_t + B` for `t ≤ n` and `z_{n+1} = z_0`, then `z_1 = z_0`. -/
theorem affine_rigid {z : ℕ → ℕ} {U V B n : ℕ} (hV : 0 < V)
    (hE : ∀ t ≤ n, U * z (t + 1) = V * z t + B) (hper : z (n + 1) = z 0) : z 1 = z 0 := by
  rcases lt_trichotomy (z 0) (z 1) with h | h | h
  · have H := chain_lt hV hE h
    have : ∀ t ≤ n, z 0 < z (t + 1) := by
      intro t
      induction t with
      | zero => intro _; exact h
      | succ t ih => intro ht; exact (ih (by omega)).trans (H (t + 1) ht)
    have := this n le_rfl; omega
  · exact h.symm
  · have H := chain_gt hV hE h
    have : ∀ t ≤ n, z (t + 1) < z 0 := by
      intro t
      induction t with
      | zero => intro _; exact h
      | succ t ih => intro ht; exact (H (t + 1) ht).trans (ih (by omega))
    have := this n le_rfl; omega

/-- **T2 (periodic cycle word ⇒ shorter cycle).** If a `T`-cycle with `r = (n+1) r'` odd steps
and length `L = (n+1) A'` (`n ≥ 1`) has an `r'`-periodic valuation word (no bad columns), then
`T^{A'}(m) = m`: the cycle is the `(n+1)`-fold repetition of a cycle of length `A'`.
Folklore; cf. Solomon (Zenodo 22220730), eq. (297) / Prop. 2.5. -/
theorem periodic_cycle_shorter {m n r' A' : ℕ} {v : ℕ → ℕ} (hr' : 1 ≤ r')
    (hv1 : ∀ i < (n + 1) * r', 1 ≤ v i) (hL : psum v ((n + 1) * r') = (n + 1) * A')
    (hodd : ∀ j < (n + 1) * A', (T^[j] m % 2 = 1 ↔ ∃ i < (n + 1) * r', psum v i = j))
    (hcyc : T^[(n + 1) * A'] m = m) (hper : badColsP n r' A' v = ∅) :
    T^[A'] m = m := by
  have hp0 : psum v 0 = 0 := by simp [psum]
  have hgood : ∀ j < r', ∀ t < n + 1, psum v (j + t * r') = psum v j + t * A' := by
    intro j hj t ht
    by_contra hne
    have : j ∈ badColsP n r' A' v := mem_filter.mpr ⟨mem_range.mpr hj, t, ht, hne⟩
    rw [hper] at this; simp at this
  have hP : ∀ t ≤ n + 1, psum v (t * r') = t * A' := by
    intro t ht
    rcases Nat.lt_or_ge t (n + 1) with h | h
    · have := hgood 0 (by omega) t h
      rwa [zero_add, hp0, zero_add] at this
    · have : t = n + 1 := by omega
      subst this; exact hL
  -- block split of the numerator
  have hsplit : ∀ t < n + 1, ∀ b ≤ r',
      Bnum (t * r' + b) v = 3 ^ b * Bnum (t * r') v + 2 ^ (t * A') * Bnum b v := by
    intro t ht b
    induction b with
    | zero => intro _; simp [Bnum]
    | succ b ih =>
      intro hb
      rw [show t * r' + (b + 1) = (t * r' + b) + 1 by ring, Bnum_succ, ih (by omega), Bnum_succ,
        show t * r' + b = b + t * r' by ring, hgood b (by omega) t ht, pow_add, pow_succ]
      ring
  -- the affine recursion for z_t = T^{t A'}(m)
  have hE : ∀ t ≤ n, 2 ^ A' * T^[(t + 1) * A'] m = 3 ^ r' * T^[t * A'] m + Bnum r' v := by
    intro t ht
    have e1 := prefix_eq hv1 hL hodd (t * r') (Nat.mul_le_mul_right _ (by omega))
    rw [hP t (by omega)] at e1
    have e2 := prefix_eq hv1 hL hodd ((t + 1) * r') (Nat.mul_le_mul_right _ (by omega))
    rw [hP (t + 1) (by omega)] at e2
    have e3 := hsplit t (by omega) r' le_rfl
    rw [show t * r' + r' = (t + 1) * r' by ring] at e3
    apply Nat.eq_of_mul_eq_mul_left (show 0 < 2 ^ (t * A') by positivity)
    calc 2 ^ (t * A') * (2 ^ A' * T^[(t + 1) * A'] m)
        = 2 ^ ((t + 1) * A') * T^[(t + 1) * A'] m := by
          rw [show (t + 1) * A' = t * A' + A' by ring, pow_add]; ring
      _ = 3 ^ ((t + 1) * r') * m + Bnum ((t + 1) * r') v := e2
      _ = 3 ^ r' * (3 ^ (t * r') * m + Bnum (t * r') v) + 2 ^ (t * A') * Bnum r' v := by
          rw [e3, show (t + 1) * r' = t * r' + r' by ring, pow_add]; ring
      _ = 2 ^ (t * A') * (3 ^ r' * T^[t * A'] m + Bnum r' v) := by rw [← e1]; ring
  have hr := affine_rigid (z := fun t => T^[t * A'] m) (show 0 < 3 ^ r' by positivity) hE
    (by simp only [zero_mul, Function.iterate_zero, id_eq]; exact hcyc)
  simpa using hr


/-- **T3 (cycle-level dichotomy, main theorem).** Let a primitive positive `T`-cycle
(least period `L`) have `r` odd steps, with `p = n + 1 ≥ 2` dividing both: `r = (n+1) r'`,
`L = (n+1) A'`. Let its odd points lie in `[m0, M]` with `2^L M ≤ 2^h 3^r m0` (roughly
`M/m0 ≤ 2^{h-1}`), `h ≤ A'`, and let `g ≥ 1` satisfy `(n r' 2^{2h+1})^2 < 2^{3(g+1)}`. Then the
valuation word has at least `r'/g` columns that are not `r'`-periodic: `r' ≤ |bad columns| · g`.
(Periodic branch: no bad column ⇒ `T^{A'} m = m`, contradicting primitivity, by T2. Otherwise:
T1 gives the balance, and `NormFold.cycle_fold_count` excludes `1 ≤ |bad| < r'/g`.) -/
theorem cycle_fold_ratio {m n r' A' h g m0 M : ℕ} {v : ℕ → ℕ} (hn : 1 ≤ n) (hr' : 1 ≤ r')
    (hm : 0 < m) (hm0 : 0 < m0)
    (hv1 : ∀ i < (n + 1) * r', 1 ≤ v i) (hL : psum v ((n + 1) * r') = (n + 1) * A')
    (hodd : ∀ j < (n + 1) * A', (T^[j] m % 2 = 1 ↔ ∃ i < (n + 1) * r', psum v i = j))
    (hcyc : T^[(n + 1) * A'] m = m)
    (hprim : ∀ ℓ, 0 < ℓ → ℓ < (n + 1) * A' → T^[ℓ] m ≠ m)
    (hlo : ∀ i < (n + 1) * r', m0 ≤ T^[psum v i] m)
    (hhi : ∀ i < (n + 1) * r', T^[psum v i] m ≤ M)
    (hR : 2 ^ ((n + 1) * A') * M ≤ 2 ^ h * 3 ^ ((n + 1) * r') * m0)
    (hhA : h ≤ A') (hg : 0 < g) (hx : (n * r' * 2 ^ (2 * h + 1)) ^ 2 < 2 ^ (3 * (g + 1))) :
    r' ≤ (badColsP n r' A' v).card * g := by
  by_contra hlt
  push Not at hlt
  rcases Nat.eq_zero_or_pos (badColsP n r' A' v).card with h0 | h0
  · have hper := card_eq_zero.mp h0
    have hA := periodic_cycle_shorter hr' hv1 hL hodd hcyc hper
    -- A' > 0: A' = psum v r' ≥ r' ≥ 1
    have hA0 : 0 < A' := by
      by_contra hA0
      have hA0 : A' = 0 := by omega
      subst hA0
      have := psum_lt hv1 (show 0 < (n + 1) * r' by positivity) le_rfl
      rw [hL] at this; simp [psum] at this
    exact hprim A' hA0 (by nlinarith) hA
  · have h2 : 2 ≤ (n + 1) * r' := by
      have := Nat.mul_le_mul hn hr'; rw [add_mul, one_mul]; omega
    obtain ⟨hq, -⟩ := NormTwo.cycle_q h2 hv1 hL hodd hcyc
    have hbal := cycle_balanced_fold hm hm0 hv1 hL hodd hcyc hlo hhi (by omega) hR
    exact cycle_fold_count hn hr' hv1 hL hodd hcyc h g hhA hbal hg hx h0 hlt

/-- **Explicit dichotomy (no primitivity assumed).** Under the hypotheses of `cycle_fold_ratio`
minus primitivity, either the valuation word is `r'`-periodic and `T^{A'} m = m` (the cycle is
an `(n+1)`-fold repetition of a shorter one), or it has at least `r'/g` non-periodic columns. -/
theorem cycle_periodic_or_far {m n r' A' h g m0 M : ℕ} {v : ℕ → ℕ} (hn : 1 ≤ n) (hr' : 1 ≤ r')
    (hm : 0 < m) (hm0 : 0 < m0)
    (hv1 : ∀ i < (n + 1) * r', 1 ≤ v i) (hL : psum v ((n + 1) * r') = (n + 1) * A')
    (hodd : ∀ j < (n + 1) * A', (T^[j] m % 2 = 1 ↔ ∃ i < (n + 1) * r', psum v i = j))
    (hcyc : T^[(n + 1) * A'] m = m)
    (hlo : ∀ i < (n + 1) * r', m0 ≤ T^[psum v i] m)
    (hhi : ∀ i < (n + 1) * r', T^[psum v i] m ≤ M)
    (hR : 2 ^ ((n + 1) * A') * M ≤ 2 ^ h * 3 ^ ((n + 1) * r') * m0)
    (hhA : h ≤ A') (hg : 0 < g) (hx : (n * r' * 2 ^ (2 * h + 1)) ^ 2 < 2 ^ (3 * (g + 1))) :
    (badColsP n r' A' v = ∅ ∧ T^[A'] m = m) ∨ r' ≤ (badColsP n r' A' v).card * g := by
  rcases Nat.eq_zero_or_pos (badColsP n r' A' v).card with h0 | h0
  · have hper := card_eq_zero.mp h0
    exact Or.inl ⟨hper, periodic_cycle_shorter hr' hv1 hL hodd hcyc hper⟩
  · right
    by_contra hlt
    push Not at hlt
    have h2 : 2 ≤ (n + 1) * r' := by
      have := Nat.mul_le_mul hn hr'; rw [add_mul, one_mul]; omega
    obtain ⟨hq, -⟩ := NormTwo.cycle_q h2 hv1 hL hodd hcyc
    have hbal := cycle_balanced_fold hm hm0 hv1 hL hodd hcyc hlo hhi (by omega) hR
    exact cycle_fold_count hn hr' hv1 hL hodd hcyc h g hhA hbal hg hx h0 hlt

/-- **Convenience form of T3.** The ratio hypothesis split as `2^L ≤ 2·3^r` (true for actual
cycles once the odd points are large compared to `r`) and `M ≤ 2^{h-1} m0`, `h ≥ 1`. -/
theorem cycle_fold_ratio' {m n r' A' h g m0 M : ℕ} {v : ℕ → ℕ} (hn : 1 ≤ n) (hr' : 1 ≤ r')
    (hm : 0 < m) (hm0 : 0 < m0)
    (hv1 : ∀ i < (n + 1) * r', 1 ≤ v i) (hL : psum v ((n + 1) * r') = (n + 1) * A')
    (hodd : ∀ j < (n + 1) * A', (T^[j] m % 2 = 1 ↔ ∃ i < (n + 1) * r', psum v i = j))
    (hcyc : T^[(n + 1) * A'] m = m)
    (hprim : ∀ ℓ, 0 < ℓ → ℓ < (n + 1) * A' → T^[ℓ] m ≠ m)
    (hlo : ∀ i < (n + 1) * r', m0 ≤ T^[psum v i] m)
    (hhi : ∀ i < (n + 1) * r', T^[psum v i] m ≤ M)
    (h1 : 1 ≤ h) (hLr : 2 ^ ((n + 1) * A') ≤ 2 * 3 ^ ((n + 1) * r'))
    (hM : M ≤ 2 ^ (h - 1) * m0)
    (hhA : h ≤ A') (hg : 0 < g) (hx : (n * r' * 2 ^ (2 * h + 1)) ^ 2 < 2 ^ (3 * (g + 1))) :
    r' ≤ (badColsP n r' A' v).card * g := by
  have hR : 2 ^ ((n + 1) * A') * M ≤ 2 ^ h * 3 ^ ((n + 1) * r') * m0 := by
    have e : 2 ^ h = 2 * 2 ^ (h - 1) := by
      rw [← pow_succ']; congr 1; omega
    calc 2 ^ ((n + 1) * A') * M ≤ (2 * 3 ^ ((n + 1) * r')) * (2 ^ (h - 1) * m0) :=
          Nat.mul_le_mul hLr hM
      _ = 2 ^ h * 3 ^ ((n + 1) * r') * m0 := by rw [e]; ring
  exact cycle_fold_ratio hn hr' hm hm0 hv1 hL hodd hcyc hprim hlo hhi hR hhA hg hx

/-- Numeric instance of T3: `r = 40902`, `L = 64832` (`n = 1`, `r' = 20451`, `A' = 32416`,
`gcd = 2`, see `NormFold.witness_fold2`), `h = 5` (`M ≲ 16 m0`), `g = 16`: the size condition
holds, so such a primitive cycle has at least `⌈20451/16⌉ = 1279` non-periodic columns. -/
theorem witness_ratio : (1 * 20451 * 2 ^ (2 * 5 + 1)) ^ 2 < 2 ^ (3 * (16 + 1)) ∧
    5 ≤ 32416 ∧ 1278 * 16 < 20451 := by
  norm_num

/-- The concrete witness word of T4: `v = (1, 3, 2, 2, …)` (length 14, sum 28). -/
def wv (i : ℕ) : ℕ := if i = 0 then 1 else if i = 1 then 3 else 2

theorem wv_bal_dec : ∀ j < 15, ∀ i < j + 1,
    (j - i) * 14 ≤ 7 * (psum wv j - psum wv i) + 7 * 1 ∧
    7 * (psum wv j - psum wv i) ≤ (j - i) * 14 + 7 * 1 := by
  decide +kernel

theorem wv_card : (badColsP 1 7 14 wv).card = 1 := by decide +kernel

/-- **T4 (non-vacuity of `NormFold.no_cycle_fold_count`, kernel-checked).** For
`n = 1`, `r' = 7`, `A' = 14`, `h = 1`, `g = 3` and the word `v = (1,3,2,…,2)` (length 14), every
hypothesis of `no_cycle_fold_count` holds (entries ≥ 1, sum 28, `1`-balanced, `3^14 + 1 < 2^28`,
size condition, exactly one bad column, `1 · 3 < 7`), hence `(2^28 - 3^14) ∤ B(v)`. -/
theorem fold_count_nonvacuous :
    3 ^ ((1 + 1) * 7) + 1 < 2 ^ ((1 + 1) * 14) ∧ 1 ≤ 14 ∧
    (∀ i < (1 + 1) * 7, 1 ≤ wv i) ∧ psum wv ((1 + 1) * 7) = (1 + 1) * 14 ∧
    (∀ i j, i ≤ j → j ≤ (1 + 1) * 7 →
        (j - i) * 14 ≤ 7 * (psum wv j - psum wv i) + 7 * 1 ∧
        7 * (psum wv j - psum wv i) ≤ (j - i) * 14 + 7 * 1) ∧
    (1 * 7 * 2 ^ (2 * 1 + 1)) ^ 2 < 2 ^ (3 * (3 + 1)) ∧
    0 < (badColsP 1 7 14 wv).card ∧ (badColsP 1 7 14 wv).card * 3 < 7 ∧
    ¬ (2 ^ ((1 + 1) * 14) - 3 ^ ((1 + 1) * 7)) ∣ Bnum ((1 + 1) * 7) wv := by
  have hq : 3 ^ ((1 + 1) * 7) + 1 < 2 ^ ((1 + 1) * 14) := by norm_num
  have hv1 : ∀ i < (1 + 1) * 7, 1 ≤ wv i := by decide
  have hsum : psum wv ((1 + 1) * 7) = (1 + 1) * 14 := by decide
  have hbal : ∀ i j, i ≤ j → j ≤ (1 + 1) * 7 →
      (j - i) * 14 ≤ 7 * (psum wv j - psum wv i) + 7 * 1 ∧
      7 * (psum wv j - psum wv i) ≤ (j - i) * 14 + 7 * 1 :=
    fun i j hij hj => wv_bal_dec j (by omega) i (by omega)
  have hx : (1 * 7 * 2 ^ (2 * 1 + 1)) ^ 2 < 2 ^ (3 * (3 + 1)) := by norm_num
  refine ⟨hq, by norm_num, hv1, hsum, hbal, hx, by rw [wv_card]; norm_num,
    by rw [wv_card]; norm_num, ?_⟩
  exact no_cycle_fold_count 1 7 14 1 3 le_rfl (by norm_num) hq (by norm_num) wv hv1 hsum hbal
    (by norm_num) hx (by rw [wv_card]; norm_num) (by rw [wv_card]; norm_num)

end Collatz.NormRatio

#print axioms Collatz.NormRatio.cycle_balanced
#print axioms Collatz.NormRatio.periodic_cycle_shorter
#print axioms Collatz.NormRatio.cycle_fold_ratio
#print axioms Collatz.NormRatio.cycle_periodic_or_far
#print axioms Collatz.NormRatio.cycle_fold_ratio'
#print axioms Collatz.NormRatio.cycle_balanced_fold
#print axioms Collatz.NormRatio.prefix_eq
#print axioms Collatz.NormRatio.witness_ratio
#print axioms Collatz.NormRatio.fold_count_nonvacuous
