import Collatz.Affine

/-!
# Minimality product inequality

Classical (Crandall 1978 / Eliahou 1993) descent inequality: if every point of a `T`-orbit
segment is `≥ m`, each odd step multiplies by at most `(3m+1)/(2m)`.  For a `T`-cycle whose
minimum is `m`, with `k` odd steps in `L` steps, `2^L m^k ≤ (3m+1)^k`, and the inequality
persists when `m` is replaced by any smaller positive `M`.
-/

namespace Collatz
open CollatzProof

/-- `S_j(n) ≤ j`. -/
theorem oddSteps_le (j n : ℕ) : oddSteps j n ≤ j := by
  induction j generalizing n with
  | zero => simp [oddSteps]
  | succ j ih =>
    simp only [oddSteps]
    have := ih (T n)
    have := Nat.mod_lt n (show 2 > 0 by norm_num)
    omega

/-- **Descent inequality.** If `m ≤ T^i(n)` for all `i < j`, then
`2^j · T^j(n) · m^{S_j(n)} ≤ (3m+1)^{S_j(n)} · n`. -/
theorem descent_product (m : ℕ) (_hm : 0 < m) : ∀ (j n : ℕ), (∀ i, i < j → m ≤ T^[i] n) →
    2 ^ j * T^[j] n * m ^ oddSteps j n ≤ (3 * m + 1) ^ oddSteps j n * n := by
  intro j
  induction j with
  | zero => intro n _; simp [oddSteps]
  | succ j ih =>
    intro n hi
    have hmn : m ≤ n := by simpa using hi 0 (by omega)
    have ih' := ih (T n) (fun i hij => by
      have := hi (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    set S := oddSteps j (T n)
    set X := T^[j] (T n)
    rw [Function.iterate_succ_apply]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h2 : 2 * T n = n := by rw [T_of_even h]; omega
      have hs : oddSteps (j + 1) n = S := by simp [oddSteps, h, S]
      rw [hs]
      calc 2 ^ (j + 1) * X * m ^ S = 2 * (2 ^ j * X * m ^ S) := by ring
        _ ≤ 2 * ((3 * m + 1) ^ S * T n) := Nat.mul_le_mul_left 2 ih'
        _ = (3 * m + 1) ^ S * (2 * T n) := by ring
        _ = (3 * m + 1) ^ S * n := by rw [h2]
    · have h2 : 2 * T n = 3 * n + 1 := by rw [T_of_odd h]; omega
      have hs : oddSteps (j + 1) n = S + 1 := by simp [oddSteps, h, S]
      rw [hs]
      have key : 2 * T n * m ≤ (3 * m + 1) * n := by
        rw [h2]; nlinarith
      calc 2 ^ (j + 1) * X * m ^ (S + 1) = (2 ^ j * X * m ^ S) * (2 * m) := by ring
        _ ≤ ((3 * m + 1) ^ S * T n) * (2 * m) := Nat.mul_le_mul_right _ ih'
        _ = (3 * m + 1) ^ S * (2 * T n * m) := by ring
        _ ≤ (3 * m + 1) ^ S * ((3 * m + 1) * n) := Nat.mul_le_mul_left _ key
        _ = (3 * m + 1) ^ (S + 1) * n := by ring

/-- **Cycle product bound.** If `m > 0` is the minimum of its `T`-orbit and `T^L m = m`,
then with `k = S_L(m)`, `2^L · m^k ≤ (3m+1)^k`. -/
theorem cycle_product_bound {m L : ℕ} (hm : 0 < m) (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m) :
    2 ^ L * m ^ oddSteps L m ≤ (3 * m + 1) ^ oddSteps L m := by
  have := descent_product m hm L m (fun i _ => hmin i)
  rw [h] at this
  have : (2 ^ L * m ^ oddSteps L m) * m ≤ (3 * m + 1) ^ oddSteps L m * m := by
    calc (2 ^ L * m ^ oddSteps L m) * m = 2 ^ L * m * m ^ oddSteps L m := by ring
      _ ≤ _ := this
  exact Nat.le_of_mul_le_mul_right this hm

/-- Monotonicity: `2^L m^k ≤ (3m+1)^k` and `0 < M ≤ m` imply `2^L M^k ≤ (3M+1)^k`. -/
theorem product_bound_mono {M m L k : ℕ} (hM : 0 < M) (hMm : M ≤ m)
    (h : 2 ^ L * m ^ k ≤ (3 * m + 1) ^ k) : 2 ^ L * M ^ k ≤ (3 * M + 1) ^ k := by
  have h1 : (3 * m + 1) * M ≤ (3 * M + 1) * m := by nlinarith
  have h2 : ((3 * m + 1) * M) ^ k ≤ ((3 * M + 1) * m) ^ k := Nat.pow_le_pow_left h1 k
  rw [mul_pow, mul_pow] at h2
  have hmk : 0 < m ^ k := Nat.pow_pos (by omega)
  have : (2 ^ L * M ^ k) * m ^ k ≤ (3 * M + 1) ^ k * m ^ k := by
    calc (2 ^ L * M ^ k) * m ^ k = (2 ^ L * m ^ k) * M ^ k := by ring
      _ ≤ (3 * m + 1) ^ k * M ^ k := Nat.mul_le_mul_right _ h
      _ ≤ _ := h2
  exact Nat.le_of_mul_le_mul_right this hmk

end Collatz

#print axioms Collatz.oddSteps_le
#print axioms Collatz.descent_product
#print axioms Collatz.cycle_product_bound
#print axioms Collatz.product_bound_mono
