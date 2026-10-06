import CollatzSearch.ProductBound

/-!
# Upper bound on the Terras remainder; cycles lie in an explicit finite range

Integer form of Terras' remainder bound: with `S = S_j(n)`,
  `2^S ρ_j(n) + 2^j 2^S ≤ 2^j 3^S`,  i.e.  `ρ_j(n) ≤ 2^{j−S}(3^S − 2^S)`
(equality when all odd steps come last).  Corollary: every point `m` of a `T`-cycle of length
`L` with `k = S_L(m)` satisfies `m (2^L − 3^k) 2^k ≤ 2^L (3^k − 2^k)`, hence (for `m, L > 0`)
`m 2^k < 2^L 3^k`.  No minimality is needed.
-/

namespace CollatzSearch
open CollatzProof

/-- **Remainder upper bound.** `2^S ρ_j(n) + 2^j 2^S ≤ 2^j 3^S` with `S = S_j(n)`. -/
theorem rho_bound (j n : ℕ) :
    2 ^ (oddSteps j n) * rho j n + 2 ^ j * 2 ^ (oddSteps j n) ≤ 2 ^ j * 3 ^ (oddSteps j n) := by
  induction j generalizing n with
  | zero => simp [oddSteps, rho]
  | succ j ih =>
    have IH := ih (T n)
    have hAB : 2 ^ oddSteps j (T n) ≤ 2 ^ j :=
      Nat.pow_le_pow_right (by norm_num) (oddSteps_le j (T n))
    set A := 2 ^ oddSteps j (T n)
    set B := 2 ^ j
    set D := 3 ^ oddSteps j (T n)
    set r := rho j (T n)
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hr : rho (j + 1) n = 2 * r := by simp [rho, h, r]
      have hs : oddSteps (j + 1) n = oddSteps j (T n) := by simp [oddSteps, h]
      rw [hr, hs, pow_succ]
      show A * (2 * r) + B * 2 * A ≤ B * 2 * D
      nlinarith
    · have hr : rho (j + 1) n = 2 * r + D := by simp [rho, h, r, D]
      have hs : oddSteps (j + 1) n = oddSteps j (T n) + 1 := by simp [oddSteps, h]
      rw [hr, hs, pow_succ, pow_succ, pow_succ]
      show A * 2 * (2 * r + D) + B * 2 * (A * 2) ≤ B * 2 * (D * 3)
      have hAD : A * D ≤ B * D := Nat.mul_le_mul_right D hAB
      nlinarith

/-- **Every cycle lies in an explicit finite range.** If `T^L m = m` and `k = S_L(m)`, then
`m 2^L 2^k + 2^L 2^k ≤ m 3^k 2^k + 2^L 3^k`, i.e. `m (2^L − 3^k) 2^k ≤ 2^L (3^k − 2^k)`. -/
theorem cycle_finite_range {m L : ℕ} (h : T^[L] m = m) :
    m * 2 ^ L * 2 ^ (oddSteps L m) + 2 ^ L * 2 ^ (oddSteps L m) ≤
      m * 3 ^ (oddSteps L m) * 2 ^ (oddSteps L m) + 2 ^ L * 3 ^ (oddSteps L m) := by
  have e := cycle_equation h
  have b := rho_bound L m
  have e2 : m * 2 ^ L * 2 ^ (oddSteps L m) =
      m * 3 ^ (oddSteps L m) * 2 ^ (oddSteps L m) + 2 ^ (oddSteps L m) * rho L m := by
    calc m * 2 ^ L * 2 ^ (oddSteps L m) = (2 ^ L * m) * 2 ^ (oddSteps L m) := by ring
      _ = (3 ^ oddSteps L m * m + rho L m) * 2 ^ (oddSteps L m) := by rw [e]
      _ = _ := by ring
  omega

/-- For a point `m > 0` of a `T`-cycle of length `L > 0`, `m 2^k < 2^L 3^k` with `k = S_L(m)`. -/
theorem cycle_lt_bound {m L : ℕ} (hm : 0 < m) (hL : 0 < L) (h : T^[L] m = m) :
    m * 2 ^ (oddSteps L m) < 2 ^ L * 3 ^ (oddSteps L m) := by
  have f := cycle_finite_range h
  have h3 := three_pow_lt_two_pow_of_cycle hm hL h
  set k := oddSteps L m
  have hpos : 0 < 2 ^ L * 2 ^ k := Nat.mul_pos (Nat.pow_pos (by norm_num))
    (Nat.pow_pos (by norm_num))
  have g : m * 2 ^ k * (3 ^ k + 1) ≤ m * 2 ^ k * 2 ^ L := Nat.mul_le_mul_left _ h3
  have e1 : m * 2 ^ L * 2 ^ k = m * 2 ^ k * 2 ^ L := by ring
  have e2 : m * 3 ^ k * 2 ^ k = m * 2 ^ k * 3 ^ k := by ring
  have e3 : m * 2 ^ k * (3 ^ k + 1) = m * 2 ^ k * 3 ^ k + m * 2 ^ k := by ring
  omega

end CollatzSearch

#print axioms CollatzSearch.rho_bound
#print axioms CollatzSearch.cycle_finite_range
#print axioms CollatzSearch.cycle_lt_bound
