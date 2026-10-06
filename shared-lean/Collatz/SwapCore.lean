import WordAlgebra
import Mathlib.Tactic

/-!
# SwapCore: S-unit identities for local moves on parity words, and the partner bound

Notation: `rhoW` is the library word numerator (`CycleWord.lean`), `p = |P|`, `s = #true S`,
`μ = #true M`, `l = |M|`, `D = 2^L - 3^k`.

* `rhoW_ctx`: if `|A| = |B|` and `#A = #B`, then
  `ρ(P A S) - ρ(P B S) = 2^p 3^s (ρ A - ρ B)` (append law, the prefix terms cancel).
* (I1) `swap_one`: `ρ(P·01·S) - ρ(P·10·S) = 2^p 3^s`.
* (I2) `swap_opp`: `ρ(P·01·M·10·S) - ρ(P·10·M·01·S) = 2^p 3^s (3^{μ+1} - 2^{l+2})`.
* (I3) `swap_same`: `ρ(P·01·M·01·S) - ρ(P·10·M·10·S) = 2^p 3^s (3^{μ+1} + 2^{l+2})`.
* (I4) `slide_false`: `ρ(P·0·1^r·S) - ρ(P·1^r·0·S) = 2^p 3^s (3^r - 2^r)`.
* (I5) `slide_true`: `ρ(P·0^r·1·S) - ρ(P·1·0^r·S) = 2^p 3^s (2^r - 1)`.
* `D_dvd_of_dvd_unit_mul`: `gcd(D,6)=1` lets one strip `2^p 3^s` from a divisibility by `D`.
* `partner_bound_minus` / `partner_bound_plus`: if `3^k < 2^L`, `u ≤ V ≤ L`, `u ≤ k`,
  `k - u ≤ L - V` and `D ∣ 3^u ∓ 2^V` (nonzero, with the partner `2^{L-V} ∓ 3^{k-u}` nonzero),
  then `D^2 ≤ 4·3^L`. The partner congruence `2^L ≡ 3^k (mod D)` turns one divisibility into two.
* `pow2_eq_pow3_add_one`: `2^L = 3^k + 1`, `k ≥ 1` ⇒ `(L,k) = (2,1)` (mod 8 argument).

Draft: `Scratch/SwapCoreDev.lean`, `Scratch/PartnerDev.lean`.
-/

namespace Collatz
open CollatzProof

/-- `ρ(10) = 1`. -/
theorem rhoW_TF : rhoW [true, false] = 1 := by decide
/-- `ρ(01) = 2`. -/
theorem rhoW_FT : rhoW [false, true] = 2 := by decide

/-- `ρ(1^r) = 3^r - 2^r` in ℤ. -/
theorem rhoW_rep_true_int (r : ℕ) : (rhoW (List.replicate r true) : ℤ) = 3^r - 2^r := by
  have := rhoW_replicate_true r
  have h : ((rhoW (List.replicate r true) + 2^r : ℕ) : ℤ) = ((3^r : ℕ) : ℤ) := by rw [this]
  push_cast at h; linarith

/-- **Context lemma.** Equal length and equal number of `true`s: `ρ(PAS) - ρ(PBS) = 2^{|P|} 3^{#S} (ρA - ρB)`. -/
theorem rhoW_ctx (P A B S : List Bool) (hl : A.length = B.length) (hc : A.count true = B.count true) :
    (rhoW (P ++ A ++ S) : ℤ) - rhoW (P ++ B ++ S) =
      2^P.length * 3^S.count true * ((rhoW A : ℤ) - rhoW B) := by
  simp only [rhoW_append, List.length_append, hl, hc]
  push_cast; ring

/-- **(I1) single adjacent swap.** `ρ(P·01·S) - ρ(P·10·S) = 2^{|P|} 3^{#S}`. -/
theorem swap_one (P S : List Bool) :
    (rhoW (P ++ [false, true] ++ S) : ℤ) - rhoW (P ++ [true, false] ++ S) =
      2^P.length * 3^S.count true := by
  rw [rhoW_ctx P [false, true] [true, false] S rfl rfl, rhoW_TF, rhoW_FT]; push_cast; ring

/-- **(I2) opposite double swap.** `ρ(P·01·M·10·S) - ρ(P·10·M·01·S) = 2^{|P|} 3^{#S} (3^{#M+1} - 2^{|M|+2})`. -/
theorem swap_opp (P M S : List Bool) :
    (rhoW (P ++ [false, true] ++ M ++ [true, false] ++ S) : ℤ)
      - rhoW (P ++ [true, false] ++ M ++ [false, true] ++ S) =
      2^P.length * 3^S.count true * (3^(M.count true + 1) - 2^(M.length + 2)) := by
  simp only [rhoW_append, List.length_append, rhoW_TF, rhoW_FT]
  simp
  ring

/-- **(I3) same-direction double swap.** `ρ(P·01·M·01·S) - ρ(P·10·M·10·S) = 2^{|P|} 3^{#S} (3^{#M+1} + 2^{|M|+2})`. -/
theorem swap_same (P M S : List Bool) :
    (rhoW (P ++ [false, true] ++ M ++ [false, true] ++ S) : ℤ)
      - rhoW (P ++ [true, false] ++ M ++ [true, false] ++ S) =
      2^P.length * 3^S.count true * (3^(M.count true + 1) + 2^(M.length + 2)) := by
  simp only [rhoW_append, List.length_append, rhoW_TF, rhoW_FT]
  simp
  ring

/-- **(I4) slide of a 0 across `r` ones.** `ρ(P·0·1^r·S) - ρ(P·1^r·0·S) = 2^{|P|} 3^{#S} (3^r - 2^r)`. -/
theorem slide_false (P S : List Bool) (r : ℕ) :
    (rhoW (P ++ [false] ++ List.replicate r true ++ S) : ℤ)
      - rhoW (P ++ List.replicate r true ++ [false] ++ S) =
      2^P.length * 3^S.count true * (3^r - 2^r) := by
  simp only [rhoW_append, List.length_append]
  simp [rhoW, rhoW_rep_true_int]
  ring

/-- **(I5) slide of a 1 across `r` zeros.** `ρ(P·0^r·1·S) - ρ(P·1·0^r·S) = 2^{|P|} 3^{#S} (2^r - 1)`. -/
theorem slide_true (P S : List Bool) (r : ℕ) :
    (rhoW (P ++ List.replicate r false ++ [true] ++ S) : ℤ)
      - rhoW (P ++ [true] ++ List.replicate r false ++ S) =
      2^P.length * 3^S.count true * (2^r - 1) := by
  simp only [rhoW_append, List.length_append, rhoW_replicate_false]
  simp [rhoW, List.count_replicate]
  ring


/-- `3 ∤ 2^L - 3^k` for `k ≥ 1`. -/
theorem not_three_dvd_D_sc {k L : ℕ} (hk : 0 < k) : ¬ (3:ℤ) ∣ 2^L - 3^k := by
  intro h
  have h2 : (3:ℤ) ∣ 2^L := by
    have : (3:ℤ) ∣ 3^k := dvd_pow_self 3 hk.ne'
    have := dvd_add h this
    simpa using this
  have h3 : (3:ℕ) ∣ 2^L := by exact_mod_cast h2
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

/-- `2 ∤ 2^L - 3^k` for `L ≥ 1`. -/
theorem not_two_dvd_D_sc {k L : ℕ} (hL : 0 < L) : ¬ (2:ℤ) ∣ 2^L - 3^k := by
  intro h
  have h2 : (2:ℤ) ∣ 3^k := by
    have : (2:ℤ) ∣ 2^L := dvd_pow_self 2 hL.ne'
    have := dvd_sub this h
    simpa using this
  have h3 : (2:ℕ) ∣ 3^k := by exact_mod_cast h2
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_two h3
  omega

/-- `D` is coprime to 3 (`k ≥ 1`). -/
theorem isCoprime_D_three {k L : ℕ} (hk : 0 < k) : IsCoprime ((2:ℤ)^L - 3^k) 3 :=
  ((Int.prime_three.irreducible).coprime_iff_not_dvd.mpr (not_three_dvd_D_sc hk)).symm

/-- `D` is coprime to 2 (`L ≥ 1`). -/
theorem isCoprime_D_two {k L : ℕ} (hL : 0 < L) : IsCoprime ((2:ℤ)^L - 3^k) 2 :=
  ((Int.prime_two.irreducible).coprime_iff_not_dvd.mpr (not_two_dvd_D_sc hL)).symm

/-- Strip an S-unit: `D ∣ 2^p 3^s N` ⇒ `D ∣ N` (`gcd(D,6)=1`). -/
theorem D_dvd_of_dvd_unit_mul {k L p s : ℕ} (hk : 0 < k) (hL : 0 < L) {N : ℤ}
    (h : ((2:ℤ)^L - 3^k) ∣ 2^p * 3^s * N) : ((2:ℤ)^L - 3^k) ∣ N := by
  have hc : IsCoprime ((2:ℤ)^L - 3^k) (2^p * 3^s) :=
    ((isCoprime_D_two hL).pow_right).mul_right (isCoprime_D_three hk).pow_right
  exact hc.dvd_of_dvd_mul_left h

/-- `D ∣ N`, `N ≠ 0` ⇒ `D ≤ |N|`. -/
theorem le_abs_of_dvd {D N : ℤ} (hN : N ≠ 0) (h : D ∣ N) : D ≤ |N| :=
  Int.le_of_dvd (abs_pos.mpr hN) ((dvd_abs D N).mpr h)

/-- **Partner bound (σ = +1).** `3^k < 2^L`, `u ≤ V ≤ L`, `u ≤ k`, `k-u ≤ L-V`, `D = 2^L-3^k` divides the nonzero `3^u - 2^V`, and the partner `2^{L-V} - 3^{k-u}` is nonzero ⇒ `D^2 ≤ 4·3^L`. -/
theorem partner_bound_minus {k L u V : ℕ} (h3 : 3^k < 2^L) (huV : u ≤ V) (hVL : V ≤ L)
    (huk : u ≤ k) (hku : k - u ≤ L - V) (hN : (3:ℤ)^u - 2^V ≠ 0)
    (hN' : (2:ℤ)^(L-V) - 3^(k-u) ≠ 0)
    (hd : ((2:ℤ)^L - 3^k) ∣ (3:ℤ)^u - 2^V) :
    ((2:ℤ)^L - 3^k)^2 ≤ 4 * 3^L := by
  set D : ℤ := (2:ℤ)^L - 3^k with hDdef
  have hDpos : 0 < D := by
    have : ((3^k : ℕ) : ℤ) < ((2^L : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at this; linarith
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h | h
    · subst h; simp at h3
    · exact h
  -- D ∣ 3^u * N'
  have hdN' : D ∣ (2:ℤ)^(L-V) - 3^(k-u) := by
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu
      have e1 : (2:ℤ)^(L-V) * 2^V = 2^L := by rw [← pow_add, Nat.sub_add_cancel hVL]
      have e : (2:ℤ)^(L-V) * (3^0 - 2^V) = ((2:ℤ)^(L-V) - 3^(k-0)) - D := by
        rw [hDdef]; simp only [pow_zero, Nat.sub_zero]; linear_combination (-1:ℤ) * e1
      have := dvd_mul_of_dvd_right hd ((2:ℤ)^(L-V))
      rw [e] at this
      have := dvd_add this (dvd_refl D)
      simpa using this
    · have hk : 0 < k := lt_of_lt_of_le hu huk
      have e : (2:ℤ)^(L-V) * (3^u - 2^V) = 3^u * ((2:ℤ)^(L-V) - 3^(k-u)) - D := by
        have e1 : (2:ℤ)^(L-V) * 2^V = 2^L := by rw [← pow_add, Nat.sub_add_cancel hVL]
        have e2 : (3:ℤ)^u * 3^(k-u) = 3^k := by rw [← pow_add, Nat.add_sub_cancel' huk]
        rw [hDdef]; linear_combination (-1:ℤ) * e1 + e2
      have := dvd_mul_of_dvd_right hd ((2:ℤ)^(L-V))
      rw [e] at this
      have := dvd_add this (dvd_refl D)
      simp only [sub_add_cancel] at this
      have hc : IsCoprime D (3^u) := (isCoprime_D_three hk).pow_right
      exact hc.dvd_of_dvd_mul_left this
  have b1 := le_abs_of_dvd hN hd
  have b2 := le_abs_of_dvd hN' hdN'
  have p1 : (3:ℤ)^u ≤ 3^V := pow_le_pow_right₀ (by norm_num) huV
  have p2 : (2:ℤ)^V ≤ 3^V := pow_le_pow_left₀ (by norm_num) (by norm_num) V
  have p3 : (3:ℤ)^(k-u) ≤ 3^(L-V) := pow_le_pow_right₀ (by norm_num) hku
  have p4 : (2:ℤ)^(L-V) ≤ 3^(L-V) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have a1 : |(3:ℤ)^u - 2^V| ≤ 2 * 3^V := by
    rw [abs_le]; constructor <;> nlinarith [pow_pos (by norm_num : (0:ℤ) < 3) u,
      pow_pos (by norm_num : (0:ℤ) < 2) V]
  have a2 : |(2:ℤ)^(L-V) - 3^(k-u)| ≤ 2 * 3^(L-V) := by
    rw [abs_le]; constructor <;> nlinarith [pow_pos (by norm_num : (0:ℤ) < 3) (k-u),
      pow_pos (by norm_num : (0:ℤ) < 2) (L-V)]
  have e3 : (3:ℤ)^V * 3^(L-V) = 3^L := by rw [← pow_add, Nat.add_sub_cancel' hVL]
  have := mul_le_mul (b1.trans a1) (b2.trans a2) hDpos.le (by positivity)
  nlinarith

/-- **Partner bound (σ = -1).** Same, with `D ∣ 3^u + 2^V` (nonzeroness automatic) ⇒ `D^2 ≤ 4·3^L`. -/
theorem partner_bound_plus {k L u V : ℕ} (h3 : 3^k < 2^L) (huV : u ≤ V) (hVL : V ≤ L)
    (huk : u ≤ k) (hku : k - u ≤ L - V)
    (hd : ((2:ℤ)^L - 3^k) ∣ (3:ℤ)^u + 2^V) :
    ((2:ℤ)^L - 3^k)^2 ≤ 4 * 3^L := by
  set D : ℤ := (2:ℤ)^L - 3^k with hDdef
  have hDpos : 0 < D := by
    have : ((3^k : ℕ) : ℤ) < ((2^L : ℕ) : ℤ) := by exact_mod_cast h3
    push_cast at this; linarith
  have hdN' : D ∣ (2:ℤ)^(L-V) + 3^(k-u) := by
    have e1 : (2:ℤ)^(L-V) * 2^V = 2^L := by rw [← pow_add, Nat.sub_add_cancel hVL]
    have e2 : (3:ℤ)^u * 3^(k-u) = 3^k := by rw [← pow_add, Nat.add_sub_cancel' huk]
    have e : (2:ℤ)^(L-V) * (3^u + 2^V) = 3^u * ((2:ℤ)^(L-V) + 3^(k-u)) + D := by
      rw [hDdef]; linear_combination e1 - e2
    have := dvd_mul_of_dvd_right hd ((2:ℤ)^(L-V))
    rw [e] at this
    have := dvd_sub this (dvd_refl D)
    simp only [add_sub_cancel_right] at this
    rcases Nat.eq_zero_or_pos u with hu | hu
    · subst hu; simpa using this
    · have hk : 0 < k := lt_of_lt_of_le hu huk
      exact ((isCoprime_D_three hk).pow_right).dvd_of_dvd_mul_left this
  have b1 := le_abs_of_dvd (by positivity) hd
  have b2 := le_abs_of_dvd (by positivity) hdN'
  have p1 : (3:ℤ)^u ≤ 3^V := pow_le_pow_right₀ (by norm_num) huV
  have p2 : (2:ℤ)^V ≤ 3^V := pow_le_pow_left₀ (by norm_num) (by norm_num) V
  have p3 : (3:ℤ)^(k-u) ≤ 3^(L-V) := pow_le_pow_right₀ (by norm_num) hku
  have p4 : (2:ℤ)^(L-V) ≤ 3^(L-V) := pow_le_pow_left₀ (by norm_num) (by norm_num) _
  have a1 : |(3:ℤ)^u + 2^V| ≤ 2 * 3^V := by
    rw [abs_of_pos (by positivity)]; linarith
  have a2 : |(2:ℤ)^(L-V) + 3^(k-u)| ≤ 2 * 3^(L-V) := by
    rw [abs_of_pos (by positivity)]; linarith
  have e3 : (3:ℤ)^V * 3^(L-V) = 3^L := by rw [← pow_add, Nat.add_sub_cancel' hVL]
  have := mul_le_mul (b1.trans a1) (b2.trans a2) hDpos.le (by positivity)
  nlinarith

/-- `3^k mod 8 ∈ {1,3}`. -/
theorem three_pow_mod_eight (k : ℕ) : 3^k % 8 = 1 ∨ 3^k % 8 = 3 := by
  induction k with
  | zero => left; rfl
  | succ k ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> simp

/-- Catalan-type special case: `2^L = 3^k + 1` forces `(L,k) ∈ {(1,0),(2,1)}`. -/
theorem pow2_eq_pow3_add_one {L k : ℕ} (h : 2^L = 3^k + 1) (hk : 0 < k) : L = 2 ∧ k = 1 := by
  have hL : L ≤ 2 := by
    by_contra hL
    have : 2^L % 8 = 0 := by
      obtain ⟨t, rfl⟩ : ∃ t, L = t + 3 := ⟨L - 3, by omega⟩
      rw [pow_add]; simp
    rcases three_pow_mod_eight k with h8 | h8 <;> omega
  have h3 : 3 ≤ 3^k := Nat.le_self_pow hk.ne' 3
  interval_cases L
  · simp at h
  · simp at h; omega
  · refine ⟨rfl, ?_⟩
    norm_num at h
    have : 3^k = 3^1 := by omega
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) this

end Collatz

#print axioms Collatz.rhoW_ctx
#print axioms Collatz.swap_one
#print axioms Collatz.swap_opp
#print axioms Collatz.swap_same
#print axioms Collatz.slide_false
#print axioms Collatz.slide_true
#print axioms Collatz.D_dvd_of_dvd_unit_mul
#print axioms Collatz.partner_bound_minus
#print axioms Collatz.partner_bound_plus
#print axioms Collatz.pow2_eq_pow3_add_one
