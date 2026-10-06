import Collatz.CycleInvariance
import Mathlib.Tactic

/-!
# Farey decomposition of cycle parameters, parametric in the verified range

Classical (Eliahou 1993, via Crandall's product bound).  If `p/q < log₂3` and
`log₂(3 + 1/M) < P/Q` are Farey neighbours (`Pq − pQ = 1`), then the pair `(k, L)`
(`k = S_L(m)` odd steps, `L` the `T`-length) of any `T`-cycle whose minimum is `≥ M` lies in the
lattice cone `k = a q + b Q`, `L = a p + b P` with `a, b ≥ 1`.  Proof: `p/q < k/L`-type
inequalities `pk < Lq` and `LQ < Pk` from `3^k < 2^L` and `2^L M^k ≤ (3M+1)^k`, then solve the
unimodular `2×2` system.  Instance at `M = 2^17`: `k = 665a + 306b`, `L = 1054a + 485b`
(so `k ≥ 971`, `L ≥ 1539`, recovering `ProductBound`/`Descent` structurally).
-/

namespace Collatz
open CollatzProof

/-- **Farey decomposition (generic, T1a).** If `P q = p Q + 1`, `2^p < 3^q`,
`(3M+1)^Q < 2^P M^Q` (`M > 0`), `3^k < 2^L` and `2^L M^k ≤ (3M+1)^k`, then there are `a, b ≥ 1`
with `k = a q + b Q` and `L = a p + b P`. -/
theorem farey_decomp {p q P Q k L M : ℕ} (hM : 0 < M) (hdet : P*q = p*Q + 1)
    (hlow : 2^p < 3^q) (hup : (3*M+1)^Q < 2^P * M^Q)
    (hk : 3^k < 2^L) (hprod : 2^L * M^k ≤ (3*M+1)^k) :
    ∃ a b, 0 < a ∧ 0 < b ∧ k = a*q + b*Q ∧ L = a*p + b*P := by
  have hq : 0 < q := by
    rcases Nat.eq_zero_or_pos q with h | h
    · subst h; simp at hlow
    · exact h
  have hkpos : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      simp at hk hprod
      have : 2 ≤ 2^L := by
        calc 2 = 2^1 := by norm_num
          _ ≤ 2^L := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hk)
      omega
    · exact h
  -- Step 1: p*k < L*q
  have s1 : p*k < L*q := by
    have e1 : (2^p)^k < (3^q)^k := Nat.pow_lt_pow_left hlow hkpos.ne'
    have e2 : (3^k)^q < (2^L)^q := Nat.pow_lt_pow_left hk hq.ne'
    rw [← pow_mul, ← pow_mul] at e1 e2
    have : 2^(p*k) < 2^(L*q) := by
      calc 2^(p*k) < 3^(q*k) := e1
        _ = 3^(k*q) := by rw [mul_comm]
        _ < 2^(L*q) := e2
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  -- Step 2: L*Q < P*k
  have s2 : L*Q < P*k := by
    have e1 : (2^L * M^k)^Q ≤ ((3*M+1)^k)^Q := Nat.pow_le_pow_left hprod Q
    have e2 : ((3*M+1)^Q)^k < (2^P * M^Q)^k := Nat.pow_lt_pow_left hup hkpos.ne'
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at e1
    rw [mul_pow, ← pow_mul, ← pow_mul, ← pow_mul] at e2
    have hMpos : 0 < M^(k*Q) := by positivity
    have : 2^(L*Q) * M^(k*Q) < 2^(P*k) * M^(k*Q) := by
      calc 2^(L*Q) * M^(k*Q) ≤ (3*M+1)^(k*Q) := e1
        _ = (3*M+1)^(Q*k) := by rw [mul_comm k Q]
        _ < 2^(P*k) * M^(Q*k) := e2
        _ = 2^(P*k) * M^(k*Q) := by rw [mul_comm Q k]
    have := Nat.lt_of_mul_lt_mul_right this
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
  refine ⟨P*k - L*Q, L*q - p*k, by omega, by omega, ?_, ?_⟩
  · have hdet' : (P:ℤ)*q = p*Q + 1 := by exact_mod_cast hdet
    have h1 : L*Q ≤ P*k := s2.le
    have h2 : p*k ≤ L*q := s1.le
    zify [h1, h2]
    linear_combination (-(k:ℤ)) * hdet'
  · have hdet' : (P:ℤ)*q = p*Q + 1 := by exact_mod_cast hdet
    have h1 : L*Q ≤ P*k := s2.le
    have h2 : p*k ≤ L*q := s1.le
    zify [h1, h2]
    linear_combination (-(L:ℤ)) * hdet'

/-- **Farey decomposition for cycles (T1b).** Let `m ≥ M > 0` be the minimum of a `T`-cycle
of length `L > 0`, and let `(p,q,P,Q)` satisfy the Farey hypotheses at `M`.  Then
`S_L(m) = a q + b Q` and `L = a p + b P` for some `a, b ≥ 1`. -/
theorem cycle_farey_decomp {m L M p q P Q : ℕ} (hM : 0 < M) (hMm : M ≤ m) (hL : 0 < L)
    (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m) (hdet : P*q = p*Q+1) (hlow : 2^p < 3^q)
    (hup : (3*M+1)^Q < 2^P * M^Q) :
    ∃ a b, 0 < a ∧ 0 < b ∧ oddSteps L m = a*q + b*Q ∧ L = a*p + b*P := by
  have hm : 0 < m := lt_of_lt_of_le hM hMm
  exact farey_decomp hM hdet hlow hup (three_pow_lt_two_pow_of_cycle hm hL h)
    (product_bound_mono hM hMm (cycle_product_bound hm h hmin))

/-- `1054/665 < log₂3` (kernel). -/
theorem farey17_low : 2^1054 < 3^665 := by decide +kernel
/-- `log₂(3 + 2^{-17}) < 485/306` (kernel). -/
theorem farey17_up : (3*2^17+1)^306 < 2^485 * (2^17)^306 := by decide +kernel

/-- **T1c.** A nontrivial positive `C`-cycle through `n` has an odd minimum `m`,
`2^17 ≤ m ≤ n`, on a `T`-cycle of length `L > 0` with `S_L(m) = 665a + 306b`,
`L = 1054a + 485b`, `a, b ≥ 1`. -/
theorem nontrivial_C_cycle_farey17 (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4) : ∃ m L a b, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧
    T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧ 0 < a ∧ 0 < b ∧ oddSteps L m = 665*a + 306*b ∧
    L = 1054*a + 485*b := by
  obtain ⟨m, L, hodd, h17, hmn, hL, hc, hmin, -⟩ := nontrivial_C_cycle_bounds' n hn ℓ hℓ h hne
  obtain ⟨a, b, ha, hb, hk, hLe⟩ := cycle_farey_decomp (M := 2^17) (by norm_num) h17 hL hc hmin
    (by norm_num : 485*665 = 1054*306+1) farey17_low farey17_up
  exact ⟨m, L, a, b, hodd, h17, hmn, hL, hc, hmin, ha, hb, by rw [hk]; ring, by rw [hLe]; ring⟩

/-- Non-vacuity: `k = 971`, `L = 1539` satisfy the hypotheses at `M = 2^17` (`a = b = 1`). -/
example : ∃ a b, 0 < a ∧ 0 < b ∧ 971 = a*665 + b*306 ∧ 1539 = a*1054 + b*485 :=
  farey_decomp (M := 2^17) (by norm_num) (by norm_num) farey17_low farey17_up
    (by decide +kernel) (by decide +kernel)

end Collatz

#print axioms Collatz.farey_decomp
#print axioms Collatz.cycle_farey_decomp
#print axioms Collatz.farey17_low
#print axioms Collatz.farey17_up
#print axioms Collatz.nontrivial_C_cycle_farey17
