import CollatzSearch.ProductBound

/-!
# The Diophantine form of the cycle product bound

For the minimum `m > 0` of a `T`-cycle of length `L` with `k = S_L(m)` odd steps, the
Crandall/Eliahou product bound `2^L m^k ≤ (3m+1)^k` implies, via a natural-number
Bernoulli inequality, the closed-form inequality
  `3m (2^L − 3^k) ≤ k 2^L`,   i.e.   `0 < 1 − 3^k/2^L ≤ k/(3m)`,
valid for all `k` with no case loop.  Consequences: `3 ρ_L(m) ≤ k 2^L`, and when `2k ≤ 3m`,
`2^{L-1} < 3^k < 2^L`, i.e. `L = ⌊k log₂ 3⌋ + 1`.

Remark: this is the classical statement that `k/L` approximates `log₂ 3` to within about
`k/(3m)`.  Closing the problem along this route needs a lower bound for `|L log 2 − k log 3|`
(Baker / Rhin linear forms in logarithms), which is not formalized here.
-/

namespace CollatzSearch
open CollatzProof

/-- Bernoulli in `ℕ`: for `k ≤ x`, `x^k (x − k) ≤ x (x − 1)^k`
(i.e. `(1 − 1/x)^k ≥ 1 − k/x`). -/
theorem bernoulli_nat (x k : ℕ) (hk : k ≤ x) : x ^ k * (x - k) ≤ x * (x - 1) ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have ih := ih (by omega)
    obtain ⟨a, rfl⟩ : ∃ a, x = k + 1 + a := ⟨x - (k + 1), by omega⟩
    have e1 : k + 1 + a - (k + 1) = a := by omega
    have e2 : k + 1 + a - k = a + 1 := by omega
    have e3 : k + 1 + a - 1 = k + a := by omega
    rw [e1, e3]; rw [e2, e3] at ih
    have key : (k + 1 + a) * a ≤ (a + 1) * (k + a) := by nlinarith
    calc (k + 1 + a) ^ (k + 1) * a = (k + 1 + a) ^ k * ((k + 1 + a) * a) := by ring
      _ ≤ (k + 1 + a) ^ k * ((a + 1) * (k + a)) := Nat.mul_le_mul_left _ key
      _ = ((k + 1 + a) ^ k * (a + 1)) * (k + a) := by ring
      _ ≤ ((k + 1 + a) * (k + a) ^ k) * (k + a) := Nat.mul_le_mul_right _ ih
      _ = (k + 1 + a) * (k + a) ^ (k + 1) := by ring

/-- For `k ≤ x`, `(x+1)^k (x − k) ≤ x^{k+1}`. -/
theorem pow_succ_mul_sub_le (x k : ℕ) (hk : k ≤ x) : (x + 1) ^ k * (x - k) ≤ x ^ (k + 1) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · obtain rfl : k = 0 := by omega
    simp
  have h1 : (x + 1) * (x - 1) ≤ x ^ 2 := by
    obtain ⟨b, rfl⟩ : ∃ b, x = b + 1 := ⟨x - 1, by omega⟩
    rw [show b + 1 - 1 = b by omega]; nlinarith
  have h2 : (x + 1) ^ k * (x - 1) ^ k ≤ x ^ (2 * k) := by
    rw [← mul_pow, pow_mul]; exact Nat.pow_le_pow_left h1 k
  have hb := bernoulli_nat x k hk
  have hxk : 0 < x ^ k := Nat.pow_pos hx
  apply Nat.le_of_mul_le_mul_left _ hxk
  calc x ^ k * ((x + 1) ^ k * (x - k)) = (x + 1) ^ k * (x ^ k * (x - k)) := by ring
    _ ≤ (x + 1) ^ k * (x * (x - 1) ^ k) := Nat.mul_le_mul_left _ hb
    _ = x * ((x + 1) ^ k * (x - 1) ^ k) := by ring
    _ ≤ x * x ^ (2 * k) := Nat.mul_le_mul_left _ h2
    _ = x ^ k * x ^ (k + 1) := by ring

/-- From the product bound `2^L m^k ≤ (3m+1)^k` (`m > 0`):
`2^L (3m) ≤ 3^k (3m) + k 2^L`, i.e. `3m(2^L − 3^k) ≤ k 2^L`. -/
theorem diophantine_of_product {m L k : ℕ} (hm : 0 < m) (hP : 2 ^ L * m ^ k ≤ (3 * m + 1) ^ k) :
    2 ^ L * (3 * m) ≤ 3 ^ k * (3 * m) + k * 2 ^ L := by
  rcases Nat.lt_or_ge (3 * m) k with hk | hk
  · have : 2 ^ L * (3 * m) ≤ k * 2 ^ L := by
      rw [mul_comm]; exact Nat.mul_le_mul_right _ hk.le
    omega
  set x := 3 * m with hx
  have hx0 : 0 < x := by omega
  -- 2^L x^k ≤ 3^k (x+1)^k
  have h1 : 2 ^ L * x ^ k ≤ 3 ^ k * (x + 1) ^ k := by
    have := Nat.mul_le_mul_left (3 ^ k) hP
    calc 2 ^ L * x ^ k = 3 ^ k * (2 ^ L * m ^ k) := by rw [hx, mul_pow]; ring
      _ ≤ _ := this
  have h2 := pow_succ_mul_sub_le x k hk
  have hxk : 0 < x ^ k := Nat.pow_pos hx0
  have h3 : 2 ^ L * (x - k) ≤ 3 ^ k * x := by
    apply Nat.le_of_mul_le_mul_left _ hxk
    calc x ^ k * (2 ^ L * (x - k)) = (2 ^ L * x ^ k) * (x - k) := by ring
      _ ≤ (3 ^ k * (x + 1) ^ k) * (x - k) := Nat.mul_le_mul_right _ h1
      _ = 3 ^ k * ((x + 1) ^ k * (x - k)) := by ring
      _ ≤ 3 ^ k * x ^ (k + 1) := Nat.mul_le_mul_left _ h2
      _ = x ^ k * (3 ^ k * x) := by ring
  have h4 : 2 ^ L * x = 2 ^ L * (x - k) + k * 2 ^ L := by
    rw [mul_comm k, ← mul_add, Nat.sub_add_cancel hk]
  omega

/-- **Cycle Diophantine inequality.** For the minimum `m > 0` of a `T`-cycle of length `L`,
with `k = S_L(m)`: `3m (2^L − 3^k) ≤ k 2^L` (stated without subtraction). -/
theorem cycle_diophantine {m L : ℕ} (hm : 0 < m) (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m) :
    2 ^ L * (3 * m) ≤ 3 ^ (oddSteps L m) * (3 * m) + oddSteps L m * 2 ^ L :=
  diophantine_of_product hm (cycle_product_bound hm h hmin)

/-- For the minimum `m > 0` of a `T`-cycle of length `L`: `3 ρ_L(m) ≤ S_L(m) 2^L`. -/
theorem cycle_rho_le {m L : ℕ} (hm : 0 < m) (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m) :
    3 * rho L m ≤ oddSteps L m * 2 ^ L := by
  have e := cycle_equation h
  have d := cycle_diophantine hm h hmin
  have e3 : 2 ^ L * (3 * m) = 3 ^ oddSteps L m * (3 * m) + 3 * rho L m := by
    rw [show 2 ^ L * (3 * m) = 3 * (2 ^ L * m) by ring, e]; ring
  omega

/-- Product bound plus `2k ≤ 3m` gives `2^L ≤ 2·3^k`. -/
theorem two_pow_le_two_mul_three_pow {m L k : ℕ} (hm : 0 < m)
    (hP : 2 ^ L * m ^ k ≤ (3 * m + 1) ^ k) (hk : 2 * k ≤ 3 * m) : 2 ^ L ≤ 2 * 3 ^ k := by
  have d := diophantine_of_product hm hP
  have h1 : 2 * k * 2 ^ L ≤ 3 * m * 2 ^ L := Nat.mul_le_mul_right _ hk
  have h2 : 2 ^ L * (3 * m) ≤ (2 * 3 ^ k) * (3 * m) := by
    have : 2 * (2 ^ L * (3 * m)) ≤ 2 * (3 ^ k * (3 * m)) + 2 * k * 2 ^ L := by
      rw [mul_assoc 2 k]; omega
    have e : 3 * m * 2 ^ L = 2 ^ L * (3 * m) := by ring
    have e2 : (2 * 3 ^ k) * (3 * m) = 2 * (3 ^ k * (3 * m)) := by ring
    omega
  exact Nat.le_of_mul_le_mul_right h2 (by omega)

/-- **`L` is determined by `k`.** For the minimum `m > 0` of a `T`-cycle of length `L > 0`
with `k = S_L(m)` and `2k ≤ 3m`: `2^{L-1} < 3^k < 2^L`, i.e. `L = ⌊k log₂ 3⌋ + 1`. -/
theorem cycle_L_determined {m L : ℕ} (hm : 0 < m) (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m)
    (hk : 2 * oddSteps L m ≤ 3 * m) (hL : 0 < L) :
    2 ^ (L - 1) < 3 ^ (oddSteps L m) ∧ 3 ^ (oddSteps L m) < 2 ^ L := by
  refine ⟨?_, three_pow_lt_two_pow_of_cycle hm hL h⟩
  have hle := two_pow_le_two_mul_three_pow hm (cycle_product_bound hm h hmin) hk
  have hpos := oddSteps_pos_of_cycle hm hL h
  have hsplit : 2 ^ L = 2 * 2 ^ (L - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hsplit] at hle
  have hle' : 2 ^ (L - 1) ≤ 3 ^ oddSteps L m := by omega
  rcases Nat.lt_or_ge 0 (L - 1) with hL1 | hL1
  · have hodd := three_pow_mod_two (oddSteps L m)
    have heven : 2 ^ (L - 1) % 2 = 0 := by
      obtain ⟨c, hc⟩ : ∃ c, L - 1 = c + 1 := ⟨L - 2, by omega⟩
      rw [hc, pow_succ]; simp
    rcases Nat.lt_or_ge (2 ^ (L - 1)) (3 ^ oddSteps L m) with h' | h'
    · exact h'
    · omega
  · have : L - 1 = 0 := by omega
    rw [this]
    have : 3 ^ 1 ≤ 3 ^ oddSteps L m := Nat.pow_le_pow_right (by norm_num) hpos
    simp at this ⊢; omega

end CollatzSearch

#print axioms CollatzSearch.bernoulli_nat
#print axioms CollatzSearch.pow_succ_mul_sub_le
#print axioms CollatzSearch.diophantine_of_product
#print axioms CollatzSearch.cycle_diophantine
#print axioms CollatzSearch.cycle_rho_le
#print axioms CollatzSearch.two_pow_le_two_mul_three_pow
#print axioms CollatzSearch.cycle_L_determined
