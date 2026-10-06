import CollatzSearch.CycleInvariance
import CollatzSearch.OneCircuit
import CollatzSearch.CycleBasic
import Mathlib.Tactic

/-!
# Terras stopping time and the "Bucket 2" finite range

Notation: `S_j = oddSteps j n`, `ρ_j = rho j n`, so that `2^j T^j(n) = 3^{S_j} n + ρ_j`
(`affine_T_iterate`).

* T1 (`oddSteps_succ_right`, `rho_succ_right`, `rho_le_of_prefix`): the append-one-step
  recursions `S_{j+1} = S_j + (T^j n mod 2)` and `ρ_{j+1} = 3ρ_j + 2^j` (odd) / `ρ_j` (even),
  and the **stopping-time remainder bound**: if every proper prefix is expanding
  (`2^i < 3^{S_i}` for `1 ≤ i < t`) and step `t` is contracting (`3^{S_t} < 2^t`), then
  `2ρ_t ≤ S_t·2^t`.  This is exponentially sharper than `rho_bound` (`ρ ≲ 2^{t−S}3^S`).
* T2 (`nondescending_bound`, `exists_stopping`, `cycle_min_stopping_bound`,
  `nontrivial_C_cycle_stopping`): a point that does not descend at its stopping time `t`
  satisfies `2n(2^t − 3^{S_t}) ≤ S_t 2^t` (the "Bucket 2" range of our notes,
  Terras 1976 Thm 2.1–2.2), and every nontrivial `C`-cycle has an odd minimum `m ≥ 2^17`
  whose Terras stopping time `2 ≤ t ≤ L` satisfies `2^{t−1} < 3^s < 2^t`
  (i.e. `s = ⌊t/log₂3⌋ (= ⌊t·log₃2⌋)`), `s ≤ S_L(m)`, and that bound.
* T3b (`T_modEq_step`, `oddSteps_modEq`, `stopping_data_modEq`): Terras periodicity — the
  parity vector of length `k`, hence `S_j` for `j ≤ k` and the stopping-time data at `t`,
  depend only on `n mod 2^k`.

Classical (Terras 1976) plus our notes (stopping-time-notes.tex, Prop "Bucket 2");
formalized here for the first time.  A structural rung, not progress on the Goal.
-/

namespace CollatzSearch
open CollatzProof

example : rho 4 3 = 5 ∧ oddSteps 4 3 = 2 := by decide

/-- Append one step on the right: `S_{j+1}(n) = S_j(n) + (T^j n mod 2)`. -/
theorem oddSteps_succ_right (j n : ℕ) : oddSteps (j+1) n = oddSteps j n + (T^[j] n) % 2 := by
  rw [oddSteps_add j 1 n]; simp [oddSteps]

/-- Append one step on the right: `ρ_{j+1}(n) = 3ρ_j(n) + 2^j` if `T^j n` is odd, else `ρ_j(n)`. -/
theorem rho_succ_right (j n : ℕ) :
    rho (j+1) n = if (T^[j] n) % 2 = 1 then 3 * rho j n + 2^j else rho j n := by
  have E1 := affine_T_iterate j n
  have E2 := affine_T_iterate (j+1) n
  rw [Function.iterate_succ_apply', oddSteps_succ_right] at E2
  set y := T^[j] n
  rcases Nat.mod_two_eq_zero_or_one y with hy | hy
  · have h2 := two_mul_T_even hy
    rw [hy, add_zero] at E2
    rw [hy]; simp only [show (0:ℕ) ≠ 1 by decide, ite_false]
    have : 2 ^ (j+1) * T y = 2^j * y := by rw [pow_succ, mul_assoc, h2]
    omega
  · have h2 := two_mul_T_odd hy
    rw [hy] at E2
    rw [hy]; simp only [ite_true]
    have : 2 ^ (j+1) * T y = 3 ^ (oddSteps j n + 1) * n + (3 * rho j n + 2^j) := by
      rw [pow_succ, mul_assoc, h2, pow_succ]
      calc 2^j * (3*y+1) = 3 * (2^j*y) + 2^j := by ring
        _ = _ := by rw [E1]; ring
    omega

/-- **Stopping-time remainder bound (T1).** If `2^i < 3^{S_i(n)}` for all `1 ≤ i < t` and
`3^{S_t(n)} < 2^t`, then `2ρ_t(n) ≤ S_t(n)·2^t`. -/
theorem rho_le_of_prefix (n t : ℕ)
    (hpre : ∀ i, 1 ≤ i → i < t → 2^i < 3^(oddSteps i n))
    (hstop : 3^(oddSteps t n) < 2^t) :
    2 * rho t n ≤ oddSteps t n * 2^t := by
  set A := 3^(oddSteps t n) with hA
  have P : ∀ j, j ≤ t → 2 * A * rho j n ≤ oddSteps j n * 2^t * 3^(oddSteps j n) := by
    intro j
    induction j with
    | zero => intro _; simp [rho]
    | succ j ih =>
      intro hj
      have ih := ih (by omega)
      rw [rho_succ_right, oddSteps_succ_right]
      rcases Nat.mod_two_eq_zero_or_one (T^[j] n) with hy | hy
      · rw [hy]; simp only [show (0:ℕ) ≠ 1 by decide, ite_false, add_zero]; exact ih
      · rw [hy]; simp only [ite_true]
        have star : 2 * A * 2^j ≤ 2^t * 3^(oddSteps j n + 1) := by
          rcases Nat.lt_or_ge (j+1) t with hlt | hge
          · have h1 := hpre (j+1) (by omega) hlt
            rw [oddSteps_succ_right, hy] at h1
            have := Nat.mul_le_mul h1.le hstop.le
            calc 2 * A * 2^j = 2^(j+1) * A := by rw [pow_succ]; ring
              _ ≤ 3 ^ (oddSteps j n + 1) * 2^t := this
              _ = _ := mul_comm _ _
          · have ht : t = j + 1 := by omega
            have hS : oddSteps t n = oddSteps j n + 1 := by
              rw [ht, oddSteps_succ_right, hy]
            rw [hA, hS, ht, pow_succ 2 j]; apply le_of_eq; ring
        have e : (oddSteps j n + 1) * 2^t * 3^(oddSteps j n + 1)
            = 3 * (oddSteps j n * 2^t * 3^(oddSteps j n)) + 2^t * 3^(oddSteps j n + 1) := by
          ring
        rw [e]
        calc 2 * A * (3 * rho j n + 2^j) = 3 * (2 * A * rho j n) + 2 * A * 2^j := by ring
          _ ≤ _ := add_le_add (Nat.mul_le_mul_left 3 ih) star
  have h := P t le_rfl
  have hApos : 0 < A := by positivity
  have : A * (2 * rho t n) ≤ A * (oddSteps t n * 2^t) := by
    calc A * (2 * rho t n) = 2 * A * rho t n := by ring
      _ ≤ _ := h
      _ = _ := by rw [← hA]; ring
  exact Nat.le_of_mul_le_mul_left this hApos

/-- **Bucket-2 range (T2a).** Under the hypotheses of `rho_le_of_prefix`, if `n ≤ T^t n`
then `2n·2^t ≤ 2n·3^{S_t} + S_t·2^t`, i.e. `2n(2^t − 3^{S_t}) ≤ S_t·2^t`. -/
theorem nondescending_bound (n t : ℕ)
    (hpre : ∀ i, 1 ≤ i → i < t → 2^i < 3^(oddSteps i n))
    (hstop : 3^(oddSteps t n) < 2^t) (hle : n ≤ T^[t] n) :
    2 * n * 2^t ≤ 2 * n * 3^(oddSteps t n) + oddSteps t n * 2^t := by
  have E := affine_T_iterate t n
  have R := rho_le_of_prefix n t hpre hstop
  have h1 : 2^t * n ≤ 2^t * T^[t] n := Nat.mul_le_mul_left _ hle
  have : 2 * n * 2^t = 2 * (2^t * n) := by ring
  have h3 : 2 * n * 3^(oddSteps t n) = 2 * (3^(oddSteps t n) * n) := by ring
  omega

/-- Non-vacuity of `nondescending_bound`: the trivial cycle point `n = 1` with stopping time
`t = 2` (`S_1 = 1`, `S_2 = 1`, `T^2 1 = 1`) satisfies all hypotheses; the conclusion reads
`8 ≤ 6 + 4`. -/
example : 2 * 1 * 2^2 ≤ 2 * 1 * 3^(oddSteps 2 1) + oddSteps 2 1 * 2^2 :=
  nondescending_bound 1 2
    (fun i h1 h2 => by obtain rfl : i = 1 := by omega
                       decide)
    (by decide) (by decide)

/-- `S_j(n)` is monotone in `j`. -/
theorem oddSteps_mono {a b : ℕ} (n : ℕ) (h : a ≤ b) : oddSteps a n ≤ oddSteps b n := by
  obtain ⟨c, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [oddSteps_add]; omega

/-- **Existence of the stopping time (T2b).** If `0 < L` and `3^{S_L(n)} < 2^L`, there is a
least `t ∈ [1, L]` with `3^{S_t} < 2^t`; all proper prefixes satisfy `2^i < 3^{S_i}`
(strict, since `2^i` is even and `3^{S_i}` odd). -/
theorem exists_stopping (n L : ℕ) (hL : 0 < L) (h : 3^(oddSteps L n) < 2^L) :
    ∃ t, 1 ≤ t ∧ t ≤ L ∧ 3^(oddSteps t n) < 2^t ∧
      ∀ i, 1 ≤ i → i < t → 2^i < 3^(oddSteps i n) := by
  classical
  have hex : ∃ t, 1 ≤ t ∧ 3^(oddSteps t n) < 2^t := ⟨L, hL, h⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, Nat.find_min' hex ⟨hL, h⟩,
    (Nat.find_spec hex).2, ?_⟩
  intro i hi1 hit
  have hn := Nat.find_min hex hit
  have hle : 2^i ≤ 3^(oddSteps i n) := by
    by_contra hc; exact hn ⟨hi1, by omega⟩
  refine lt_of_le_of_ne hle ?_
  intro heq
  have h2 : 2 ∣ 2^i := dvd_pow_self 2 (by omega)
  have h3 := three_pow_mod_two (oddSteps i n)
  omega

/-- Stopping data for a cycle minimum `m > 0` of a `T`-cycle of length `L > 0` (no minimality
needed): a Terras stopping time `1 ≤ t ≤ L` with the prefix condition kept. -/
theorem cycle_min_stopping_data {m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    (h : T^[L] m = m) :
    ∃ t, 1 ≤ t ∧ t ≤ L ∧ oddSteps t m ≤ oddSteps L m ∧
      3^(oddSteps t m) < 2^t ∧ (∀ i, 1 ≤ i → i < t → 2^i < 3^(oddSteps i m)) ∧
      (2 ≤ t → 2^(t-1) < 3^(oddSteps t m)) := by
  obtain ⟨t, h1, h2, h3, h4⟩ := exists_stopping m L hL (three_pow_lt_two_pow_of_cycle hm hL h)
  refine ⟨t, h1, h2, oddSteps_mono m h2, h3, h4, fun ht => ?_⟩
  exact lt_of_lt_of_le (h4 (t-1) (by omega) (by omega))
    (Nat.pow_le_pow_right (by norm_num) (oddSteps_mono m (by omega)))

/-- **Cycle-minimum stopping bound (T2c).** The minimum `m > 0` of a `T`-cycle of length
`L > 0` has a stopping time `1 ≤ t ≤ L` with `s = S_t(m) ≤ S_L(m)`, `3^s < 2^t`,
`2^{t−1} < 3^s` when `t ≥ 2`, and `2m·2^t ≤ 2m·3^s + s·2^t`. -/
theorem cycle_min_stopping_bound {m L : ℕ} (hm : 0 < m) (hL : 0 < L)
    (h : T^[L] m = m) (hmin : ∀ j, m ≤ T^[j] m) :
    ∃ t, 1 ≤ t ∧ t ≤ L ∧ oddSteps t m ≤ oddSteps L m ∧
      3^(oddSteps t m) < 2^t ∧ (2 ≤ t → 2^(t-1) < 3^(oddSteps t m)) ∧
      2 * m * 2^t ≤ 2 * m * 3^(oddSteps t m) + oddSteps t m * 2^t := by
  obtain ⟨t, h1, h2, h3, h4, h5, h6⟩ := cycle_min_stopping_data hm hL h
  exact ⟨t, h1, h2, h3, h4, h6, nondescending_bound m t h5 h4 (hmin t)⟩

/-- `S_1(m) = 1` for odd `m`. -/
theorem oddSteps_one_of_odd {m : ℕ} (hm : m % 2 = 1) : oddSteps 1 m = 1 := by
  simp [oddSteps, hm]

/-- **Goal-shaped stopping bound (T2d).** A nontrivial positive `C`-cycle through `n` has an
odd minimum `m`, `2^17 ≤ m ≤ n`, on a `T`-cycle of length `L > 0`, whose Terras stopping time
`t` (with `2 ≤ t ≤ L`) satisfies `2^{t−1} < 3^s < 2^t` (so `s = ⌊t/log₂3⌋ (= ⌊t·log₃2⌋)`),
`s = S_t(m) ≤ S_L(m)`, and `2m(2^t − 3^s) ≤ s·2^t`. -/
theorem nontrivial_C_cycle_stopping (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) (h1 : n ≠ 1) (h2 : n ≠ 2) (h4 : n ≠ 4) :
    ∃ m L t, m % 2 = 1 ∧ 2^17 ≤ m ∧ m ≤ n ∧ 0 < L ∧ T^[L] m = m ∧ (∀ j, m ≤ T^[j] m) ∧
      2 ≤ t ∧ t ≤ L ∧ oddSteps t m ≤ oddSteps L m ∧
      2^(t-1) < 3^(oddSteps t m) ∧ 3^(oddSteps t m) < 2^t ∧
      2 * m * 2^t ≤ 2 * m * 3^(oddSteps t m) + oddSteps t m * 2^t := by
  obtain ⟨m, L, hodd, h17, hmn, hL, hc, hmin, -⟩ := nontrivial_C_cycle_bounds' n hn ℓ hℓ h ⟨h1, h2, h4⟩
  have hm : 0 < m := lt_of_lt_of_le (by norm_num) h17
  obtain ⟨t, ht1, ht2, ht3, ht4, ht5, ht6⟩ := cycle_min_stopping_bound hm hL hc hmin
  have ht : 2 ≤ t := by
    by_contra hc'
    have : t = 1 := by omega
    subst this
    rw [oddSteps_one_of_odd hodd] at ht4; norm_num at ht4
  exact ⟨m, L, t, hodd, h17, hmn, hL, hc, hmin, ht, ht2, ht3, ht5 ht, ht4, ht6⟩

/-- One Collatz step respects congruence mod powers of two, losing one bit. -/
theorem T_modEq_step {m n n' : ℕ} (h : n ≡ n' [MOD 2^(m+1)]) :
    n % 2 = n' % 2 ∧ T n ≡ T n' [MOD 2^m] := by
  have hp : n % 2 = n' % 2 := Nat.ModEq.of_dvd (Dvd.intro_left _ (pow_succ 2 m).symm) h
  refine ⟨hp, ?_⟩
  rw [Nat.modEq_iff_dvd] at h ⊢
  obtain ⟨c, hc⟩ := h
  rcases Nat.mod_two_eq_zero_or_one n with hy | hy
  · have a := two_mul_T_even hy
    have b := two_mul_T_even (hp ▸ hy)
    refine ⟨c, ?_⟩
    have : (2:ℤ) * ((T n' : ℤ) - T n) = 2 * ((2:ℤ)^m * c) := by
      have a' : (2:ℤ) * (T n : ℤ) = n := by exact_mod_cast a
      have b' : (2:ℤ) * (T n' : ℤ) = n' := by exact_mod_cast b
      rw [mul_sub, a', b', hc]; push_cast; ring
    exact mul_left_cancel₀ (by norm_num) this
  · have a := two_mul_T_odd hy
    have b := two_mul_T_odd (hp ▸ hy)
    refine ⟨3 * c, ?_⟩
    have : (2:ℤ) * ((T n' : ℤ) - T n) = 2 * ((2:ℤ)^m * (3 * c)) := by
      have a' : (2:ℤ) * (T n : ℤ) = 3 * n + 1 := by exact_mod_cast a
      have b' : (2:ℤ) * (T n' : ℤ) = 3 * n' + 1 := by exact_mod_cast b
      rw [mul_sub, a', b']
      have : (n' : ℤ) - n = 2^(m+1) * c := by exact_mod_cast hc
      linear_combination 3 * this
    exact mul_left_cancel₀ (by norm_num) this

/-- **Terras periodicity (T3b).** If `n ≡ n' (mod 2^k)` then `S_j(n) = S_j(n')` for all `j ≤ k`
(the first `k` parities agree). -/
theorem oddSteps_modEq (k : ℕ) : ∀ {n n' : ℕ}, n ≡ n' [MOD 2^k] →
    ∀ j ≤ k, oddSteps j n = oddSteps j n' := by
  induction k with
  | zero => intro n n' _ j hj; obtain rfl : j = 0 := by omega
            rfl
  | succ m ih =>
    intro n n' h j hj
    rcases j with _ | i
    · rfl
    · obtain ⟨hp, hT⟩ := T_modEq_step h
      simp only [oddSteps]
      rw [ih hT i (by omega), hp]


/-- **Stopping data is periodic mod `2^t` (T3b corollary).** If `n ≡ n' (mod 2^t)`, the
stopping-time hypotheses (`hpre`, `hstop`) at `t` hold for `n` iff they hold for `n'`. -/
theorem stopping_data_modEq {t n n' : ℕ} (h : n ≡ n' [MOD 2^t]) :
    ((∀ i, 1 ≤ i → i < t → 2^i < 3^(oddSteps i n)) ∧ 3^(oddSteps t n) < 2^t) ↔
    ((∀ i, 1 ≤ i → i < t → 2^i < 3^(oddSteps i n')) ∧ 3^(oddSteps t n') < 2^t) := by
  have e := oddSteps_modEq t h
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun i a b => (e i b.le) ▸ h1 i a b, (e t le_rfl) ▸ h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨fun i a b => (e i b.le).symm ▸ h1 i a b, (e t le_rfl).symm ▸ h2⟩

end CollatzSearch

#print axioms CollatzSearch.oddSteps_succ_right
#print axioms CollatzSearch.rho_succ_right
#print axioms CollatzSearch.rho_le_of_prefix
#print axioms CollatzSearch.nondescending_bound
#print axioms CollatzSearch.oddSteps_mono
#print axioms CollatzSearch.exists_stopping
#print axioms CollatzSearch.cycle_min_stopping_data
#print axioms CollatzSearch.cycle_min_stopping_bound
#print axioms CollatzSearch.nontrivial_C_cycle_stopping
#print axioms CollatzSearch.T_modEq_step
#print axioms CollatzSearch.oddSteps_modEq
#print axioms CollatzSearch.stopping_data_modEq
