import Collatz.CycleBasic

/-!
# Terras affine identity and first cycle consequences

`oddSteps j n` counts the odd values among `n, T n, …, T^{j-1} n`, and `rho j n` is the
Terras remainder; both are defined by first-step recursion.  Then, in `ℕ` with no
subtraction or division,
  `2^j · T^j(n) = 3^{oddSteps j n} · n + rho j n`.

Consequences for a `T`-cycle `T^L m = m`, `m > 0`, `L > 0`: at least one odd step,
`rho > 0`, `3^k < 2^L`, `rho` odd when `m` odd, and no cycle with exactly one odd step
other than through `1`.
-/

namespace Collatz
open CollatzProof

/-- Number of odd values among `n, T n, …, T^{j-1} n`. -/
def oddSteps : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, n => oddSteps j (T n) + n % 2

/-- The Terras remainder: `rho 0 n = 0`,
`rho (j+1) n = 2·rho j (T n) + [n odd]·3^{oddSteps j (T n)}`. -/
def rho : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j + 1, n => 2 * rho j (T n) + (if n % 2 = 1 then 3 ^ oddSteps j (T n) else 0)

example : oddSteps 2 1 = 1 ∧ rho 2 1 = 1 := by decide
example : oddSteps 3 5 = 1 ∧ rho 3 5 = 1 := by decide

/-- **Terras affine identity.** `2^j · T^j(n) = 3^{S_j(n)} · n + ρ_j(n)`. -/
theorem affine_T_iterate (j n : ℕ) :
    2 ^ j * T^[j] n = 3 ^ oddSteps j n * n + rho j n := by
  induction j generalizing n with
  | zero => simp [oddSteps, rho]
  | succ j ih =>
    rw [Function.iterate_succ_apply, pow_succ, mul_comm (2 ^ j) 2, mul_assoc, ih (T n)]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h2 : 2 * T n = n := by rw [T_of_even h]; omega
      simp only [oddSteps, rho, h]
      simp
      rw [show 2 * (3 ^ oddSteps j (T n) * T n + rho j (T n))
        = 3 ^ oddSteps j (T n) * (2 * T n) + 2 * rho j (T n) by ring, h2]
    · have h2 : 2 * T n = 3 * n + 1 := by rw [T_of_odd h]; omega
      simp only [oddSteps, rho, h, ite_true]
      rw [pow_succ, show 2 * (3 ^ oddSteps j (T n) * T n + rho j (T n))
        = 3 ^ oddSteps j (T n) * (2 * T n) + 2 * rho j (T n) by ring, h2]
      ring

/-- If there are no odd steps, the remainder vanishes. -/
theorem rho_eq_zero_of_oddSteps_eq_zero {j n : ℕ} (h : oddSteps j n = 0) : rho j n = 0 := by
  induction j generalizing n with
  | zero => rfl
  | succ j ih =>
    simp only [oddSteps] at h
    have h1 : oddSteps j (T n) = 0 := by omega
    have h2 : n % 2 ≠ 1 := by omega
    simp [rho, ih h1, h2]

theorem three_pow_mod_two (k : ℕ) : 3 ^ k % 2 = 1 := by
  rw [Nat.pow_mod]; norm_num

/-- **Cycle equation.** If `T^L m = m` then `2^L · m = 3^k · m + ρ_L(m)`, `k = S_L(m)`. -/
theorem cycle_equation {m L : ℕ} (h : T^[L] m = m) :
    2 ^ L * m = 3 ^ oddSteps L m * m + rho L m := by
  have := affine_T_iterate L m
  rwa [h] at this

/-- A positive `T`-cycle has at least one odd step. -/
theorem oddSteps_pos_of_cycle {m L : ℕ} (hm : 0 < m) (hL : 0 < L) (h : T^[L] m = m) :
    0 < oddSteps L m := by
  by_contra hk
  have hk0 : oddSteps L m = 0 := by omega
  have e := cycle_equation h
  rw [hk0, rho_eq_zero_of_oddSteps_eq_zero hk0] at e
  have : 2 ≤ 2 ^ L := by
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ L := Nat.pow_le_pow_right (by norm_num) hL
  simp at e
  nlinarith

/-- On a positive `T`-cycle the remainder `ρ_L(m)` is positive. -/
theorem rho_pos_of_cycle {m L : ℕ} (hm : 0 < m) (hL : 0 < L) (h : T^[L] m = m) :
    0 < rho L m := by
  by_contra hr
  have hr0 : rho L m = 0 := by omega
  have e := cycle_equation h
  rw [hr0, add_zero] at e
  have e2 : 2 ^ L = 3 ^ oddSteps L m := Nat.eq_of_mul_eq_mul_right hm e
  have h1 := three_pow_mod_two (oddSteps L m)
  have h2 : 2 ^ L % 2 = 0 := by
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [pow_succ]; simp
  omega

/-- On a positive `T`-cycle with `k` odd steps in `L` steps, `3^k < 2^L`. -/
theorem three_pow_lt_two_pow_of_cycle {m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    (h : T^[L] m = m) : 3 ^ oddSteps L m < 2 ^ L := by
  have e := cycle_equation h
  have hr := rho_pos_of_cycle hm hL h
  have : 3 ^ oddSteps L m * m < 2 ^ L * m := by omega
  exact Nat.lt_of_mul_lt_mul_right this

/-- Unfolding for odd `m`: `ρ_{L+1}(m) = 2ρ_L(Tm) + 3^{S_L(Tm)}`. -/
theorem rho_succ_of_odd {m : ℕ} (hm : m % 2 = 1) (L : ℕ) :
    rho (L + 1) m = 2 * rho L (T m) + 3 ^ oddSteps L (T m) := by
  simp [rho, hm]

/-- If `m` is odd and `L > 0` then `ρ_L(m)` is odd. -/
theorem rho_odd_of_odd {m L : ℕ} (hm : m % 2 = 1) (hL : 0 < L) : rho L m % 2 = 1 := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  rw [rho_succ_of_odd hm]
  have := three_pow_mod_two (oddSteps L' (T m))
  omega

/-- **No 1-odd-step cycles** (trivial case of Steiner): an odd `m` on a `T`-cycle with
exactly one odd step per period is `m = 1`. -/
theorem eq_one_of_cycle_oddSteps_eq_one {m L : ℕ} (hm : m % 2 = 1) (hL : 0 < L)
    (h : T^[L] m = m) (hk : oddSteps L m = 1) : m = 1 := by
  obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
  have hk' : oddSteps L' (T m) = 0 := by
    simp only [oddSteps] at hk; omega
  have hr : rho (L' + 1) m = 1 := by
    rw [rho_succ_of_odd hm, hk', rho_eq_zero_of_oddSteps_eq_zero hk']; simp
  have e := cycle_equation h
  rw [hk, hr, pow_one] at e
  have hd : m ∣ 3 * m + 1 := ⟨2 ^ (L' + 1), by rw [← e]; ring⟩
  have : m ∣ 1 := (Nat.dvd_add_right (dvd_mul_left m 3)).mp hd
  exact Nat.dvd_one.mp this

/-- For any odd `m > 1` on a `T`-cycle of length `L > 0` (no minimality assumed): at least
two odd steps per period. -/
theorem two_le_oddSteps_of_cycle {m L : ℕ} (hm1 : 1 < m) (hm : m % 2 = 1) (hL : 0 < L)
    (h : T^[L] m = m) : 2 ≤ oddSteps L m := by
  have h0 := oddSteps_pos_of_cycle (by omega) hL h
  by_contra hlt
  have := eq_one_of_cycle_oddSteps_eq_one hm hL h (by omega)
  omega

/-- Combined reduction: the no-nontrivial-cycles statement follows from ruling out minimal
odd `m > 1` on `T`-cycles with `k = S_L(m) ≥ 2`, `3^k < 2^L` and cycle equation
`2^L m = 3^k m + ρ_L(m)`. -/
theorem goal_of_no_min_odd_T_cycle' (H : ∀ m L : ℕ, 1 < m → m % 2 = 1 → 0 < L →
      T^[L] m = m → (∀ j, m ≤ T^[j] m) → 2 ≤ oddSteps L m → 3 ^ oddSteps L m < 2 ^ L →
      2 ^ L * m = 3 ^ oddSteps L m * m + rho L m → False)
    (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n) : n = 1 ∨ n = 2 ∨ n = 4 :=
  goal_of_no_min_odd_T_cycle (fun m L h1 h2 h3 h4 h5 =>
    H m L h1 h2 h3 h4 h5 (two_le_oddSteps_of_cycle h1 h2 h3 h4)
      (three_pow_lt_two_pow_of_cycle (by omega) h3 h4) (cycle_equation h4)) n hn ℓ hℓ h

end Collatz

#print axioms Collatz.affine_T_iterate
#print axioms Collatz.rho_eq_zero_of_oddSteps_eq_zero
#print axioms Collatz.cycle_equation
#print axioms Collatz.oddSteps_pos_of_cycle
#print axioms Collatz.rho_pos_of_cycle
#print axioms Collatz.three_pow_lt_two_pow_of_cycle
#print axioms Collatz.rho_odd_of_odd
#print axioms Collatz.eq_one_of_cycle_oddSteps_eq_one
#print axioms Collatz.two_le_oddSteps_of_cycle
#print axioms Collatz.goal_of_no_min_odd_T_cycle'
#print axioms Collatz.three_pow_mod_two
#print axioms Collatz.rho_succ_of_odd
