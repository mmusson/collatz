import CollatzSearch.Runs

/-!
# Run certificate: cycles with few odd runs in a finite range

Combines the rotation-free run inequality `cycle_run_ineq` (`2^L X^r ≤ 3^k (X+1)^r` when every
cycle point is `≥ X`) with the verified lower bound `X = 2^17` (`cycle_points_ge`) and a kernel
certificate.

* `runOKX X R k` (generic in `X`, `R`; `L0 = candL k`): `2^{L0-1} ≤ 3^k` and
  `3^k (X+1)^R < 2^{L0} X^R`.  `runOKX_sound` shows that it refutes every `L` with `3^k < 2^L` and
  every `r ≤ R` obeying the run inequality; soundness never uses the accuracy of `candL`.
  A future verified lower bound `X0` on cycle elements can be plugged into `X`.
* `runRange_971_10000`: `runOKX (2^17) 53 k` holds for all `971 ≤ k < 10000` (`decide +kernel`,
  no `native_decide`, no `set_option`).
* **`runs_or_oddSteps_of_cycle`: every point `x ∉ {1,2}` of a `T`-cycle has
  `S_L(x) ≥ 10000` or `oddRuns L x ≥ 54`.**  Rotation-free.  (`oddRuns L x` is the number of
  maximal cyclic odd runs only when `L` is the minimal period and the cycle contains both
  parities; for `L = t·p`, `oddRuns_mul` in `RunsRotate.lean` gives `t` times that number.)
* `nontrivial_C_cycle_runs`: the same, stated on the Goal's hypotheses.

The certificate discriminates: `runOKX (2^17) 54 9616 = false`.  At `X = 2^17` it degrades near
the convergent denominators `15601, 47468, 79335` of `log₂ 3`, so pushing `K` much past `10^4`
at this `X` is a dead end; only a larger verified `X0` helps.

Honesty: a finite formal instance of the Simons–de Weger (2005) method with a small `X0`; not
new mathematics, and far from the Goal.
-/

namespace CollatzSearch
open CollatzProof

/-- Kernel certificate: with `L0 = candL k`, `2^{L0-1} ≤ 3^k` and `3^k (X+1)^R < 2^{L0} X^R`. -/
def runOKX (X R k : ℕ) : Bool :=
  Nat.ble (2 ^ (candL k - 1)) (3 ^ k) && Nat.ble (3 ^ k * (X+1) ^ R + 1) (2 ^ (candL k) * X ^ R)

/-- Soundness (independent of `candL` accuracy): if `r ≤ R`, `3^k < 2^L`,
`2^L X^r ≤ 3^k (X+1)^r` and `runOKX X R k`, contradiction. -/
theorem runOKX_sound {X R k L r : ℕ} (hr : r ≤ R) (hL : 3^k < 2^L)
    (h : 2^L * X^r ≤ 3^k * (X+1)^r) (hc : runOKX X R k = true) : False := by
  simp only [runOKX, Bool.and_eq_true, Nat.ble_eq] at hc
  obtain ⟨c1, c2⟩ := hc
  generalize candL k = L0 at *
  have hle : 2 ^ L0 ≤ 2 ^ L := by
    apply Nat.pow_le_pow_right (by norm_num)
    by_contra hh
    have : 2 ^ L ≤ 2 ^ (L0 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨s, rfl⟩ : ∃ s, R = r + s := ⟨R - r, by omega⟩
  rw [pow_add, pow_add] at c2
  have hs : X ^ s ≤ (X+1) ^ s := Nat.pow_le_pow_left (by omega) s
  have e1 : 2 ^ L0 * (X ^ r * X ^ s) ≤ 2 ^ L * X ^ r * X ^ s := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hle)
  have e2 : 2 ^ L * X ^ r * X ^ s ≤ 3 ^ k * (X+1) ^ r * X ^ s := Nat.mul_le_mul_right _ h
  have e3 : 3 ^ k * (X+1) ^ r * X ^ s ≤ 3 ^ k * ((X+1) ^ r * (X+1) ^ s) := by
    rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hs
  omega

/-- `runRange lo n` checks `runOKX (2^17) 53 k` for `lo ≤ k < lo + n`. -/
def runRange (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => runRange lo n && runOKX (2^17) 53 (lo + n)

theorem runRange_sound (lo : ℕ) : ∀ n, runRange lo n = true → ∀ k, lo ≤ k → k < lo + n →
    runOKX (2^17) 53 k = true := by
  intro n
  induction n with
  | zero => intro _ k h1 h2; omega
  | succ n ih =>
    intro h k h1 h2
    simp only [runRange, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge k (lo + n) with hk | hk
    · exact ih h.1 k h1 hk
    · have : k = lo + n := by omega
      subst this; exact h.2

/-- `RunRange lo hi`: `runOKX (2^17) 53 k` for all `lo ≤ k < hi`. -/
def RunRange (lo hi : ℕ) : Prop := ∀ k, lo ≤ k → k < hi → runOKX (2^17) 53 k = true

theorem runRange_nil (hi : ℕ) : RunRange hi hi := fun k h1 h2 => absurd h2 (by omega)

theorem runRange_cons {lo n hi : ℕ} (h : runRange lo n = true) (hr : RunRange (lo + n) hi) :
    RunRange lo hi := fun k h1 h2 => by
  rcases Nat.lt_or_ge k (lo + n) with hk | hk
  · exact runRange_sound lo n h k h1 hk
  · exact hr k hk h2

theorem runBlock_0 : runRange 971 1029 = true := by decide +kernel
theorem runBlock_1 : runRange 2000 1000 = true := by decide +kernel
theorem runBlock_2 : runRange 3000 1000 = true := by decide +kernel
theorem runBlock_3 : runRange 4000 1000 = true := by decide +kernel
theorem runBlock_4 : runRange 5000 1000 = true := by decide +kernel
theorem runBlock_5 : runRange 6000 1000 = true := by decide +kernel
theorem runBlock_6 : runRange 7000 1000 = true := by decide +kernel
theorem runBlock_7 : runRange 8000 1000 = true := by decide +kernel
theorem runBlock_8 : runRange 9000 1000 = true := by decide +kernel

/-- `runOKX (2^17) 53 k = true` for every `971 ≤ k < 10000` (kernel-checked). -/
theorem runRange_971_10000 : ∀ k, 971 ≤ k → k < 10000 → runOKX (2^17) 53 k = true :=
  runRange_cons runBlock_0 <| runRange_cons runBlock_1 <| runRange_cons runBlock_2 <|
  runRange_cons runBlock_3 <| runRange_cons runBlock_4 <| runRange_cons runBlock_5 <|
  runRange_cons runBlock_6 <| runRange_cons runBlock_7 <| runRange_cons runBlock_8 <|
  runRange_nil 10000

/-- Every point of a `T`-cycle through `x > 0`, `x ∉ {1,2}`, is `≥ 2^17`. -/
theorem cycle_points_ge {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (h1 : x ≠ 1) (h2 : x ≠ 2) : ∀ i, 2^17 ≤ T^[i] x := by
  obtain ⟨j0, hj0, hmin, hper⟩ := exists_cycle_min hL hc
  set M := T^[j0] x with hM
  have hxM : T^[L - j0] M = x := by
    rw [hM, ← Function.iterate_add_apply, Nat.sub_add_cancel hj0.le, hc]
  have hM1 : M ≠ 1 := by
    intro e
    rw [e] at hxM
    rcases iterate_T_one_mem (L - j0) with e' | e' <;> rw [hxM] at e' <;> contradiction
  have hMpos : 0 < M := iterate_T_pos hx j0
  have hM17 : 2^17 ≤ M := min_orbit_ge M (by omega) hmin
  intro i
  have : T^[i] x = T^[i + (L - j0)] M := by
    rw [Function.iterate_add_apply, hxM]
  rw [this]
  exact le_trans hM17 (hmin _)

/-- **Rotation-free run exclusion.** A point `x > 0`, `x ∉ {1,2}`, of a `T`-cycle of length
`L > 0` has `S_L(x) ≥ 10000` or `oddRuns L x ≥ 54`. -/
theorem runs_or_oddSteps_of_cycle {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (h1 : x ≠ 1) (h2 : x ≠ 2) : 10000 ≤ oddSteps L x ∨ 54 ≤ oddRuns L x := by
  have hineq := cycle_run_ineq hx hc (cycle_points_ge hx hL hc h1 h2)
  have h3 := three_pow_lt_two_pow_of_cycle hx hL hc
  have h971 := oddSteps_ge_of_cycle hx hL hc h1 h2
  by_contra hh
  push Not at hh
  exact runOKX_sound (R := 53) (by omega) h3 hineq (runRange_971_10000 _ h971 hh.1)

/-- A nontrivial `T`-cycle with at most `53` odd runs (in particular a 1- or 2-run cycle,
in any phase) has `S_L(x) ≥ 10000`. -/
theorem oddSteps_ge_of_few_runs {x L : ℕ} (hx : 0 < x) (hL : 0 < L) (hc : T^[L] x = x)
    (h1 : x ≠ 1) (h2 : x ≠ 2) (hr : oddRuns L x ≤ 53) : 10000 ≤ oddSteps L x := by
  have := runs_or_oddSteps_of_cycle hx hL hc h1 h2; omega

/-- Sanity: the certificate fails at `R = 54`, `k = 9616`. -/
example : runOKX (2^17) 54 9616 = false := by decide +kernel

/-- Goal-shaped corollary: a positive `C`-cycle point `n ∉ {1,2,4}` yields an odd `m`,
`2^17 ≤ m ≤ n`, on a `T`-cycle of length `L > 0`, with `S_L(m) ≥ 971` and
(`S_L(m) ≥ 10000` or `oddRuns L m ≥ 54`). -/
theorem nontrivial_C_cycle_runs (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ 971 ≤ oddSteps L m ∧
      (10000 ≤ oddSteps L m ∨ 54 ≤ oddRuns L m) := by
  obtain ⟨m, L, a1, a2, a3, a4, a5, a6, -⟩ := nontrivial_C_cycle_bounds n hn ℓ hℓ h ⟨h1, h2, h4⟩
  have : (2:ℕ)^17 = 131072 := by norm_num
  exact ⟨m, L, a1, a2, a3, a4, a5, a6,
    runs_or_oddSteps_of_cycle (by omega) a4 a5 (by omega) (by omega)⟩

end CollatzSearch

#print axioms CollatzSearch.runOKX_sound
#print axioms CollatzSearch.runRange_971_10000
#print axioms CollatzSearch.cycle_points_ge
#print axioms CollatzSearch.runs_or_oddSteps_of_cycle
#print axioms CollatzSearch.oddSteps_ge_of_few_runs
#print axioms CollatzSearch.nontrivial_C_cycle_runs
