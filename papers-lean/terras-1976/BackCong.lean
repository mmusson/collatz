import StoppingTime
import Mathlib.Tactic
import Mathlib.Data.Set.Card

/-!
# The backward congruence theorem (forward form) and cycle-class uniqueness

Notation: `S_k(n) = oddSteps k n`, the number of odd values among `n, T n, …, T^{k-1} n`.

* T1 (`shift_iterate`, `oddSteps_shift`, `iterate_shift`): the **shift lemma**
  `S_k(n + 2^k t) = S_k(n)` and `T^k(n + 2^k t) = T^k(n) + 3^{S_k(n)} t` (pure ℕ).
* T2 (`image_class_iff`, `backcong_modEq`, `modEq_of_parity`): the `T^k`-image of the
  2-adic class `n + 2^k ℕ` is exactly `{m ≥ T^k n : m ≡ T^k n mod 3^{S_k n}}` (forward form
  of the Backward Congruence Theorem of stopping-time-notes.tex, Thm backcong); the
  difference law `n ≡ n' (2^k) ⇒ S_k n = S_k n' ∧ T^k n ≡ T^k n' (3^{S_k n})`; and the
  converse of Terras periodicity: equal parity vectors of length `k` force `n ≡ n' (2^k)`.
* T3 (`cycle_shift`, `periodic_unique_mod`, `periodic_injOn_mod`, `periodic_ncard_le`):
  if `T^L x = x` then `T^L(x + 2^L t) = x + 3^{S_L x} t`; for `L > 0` each class mod `2^L`
  contains at most one fixed point of `T^L` (Böhm–Sontacchi uniqueness, dynamical form);
  hence `{x | T^L x = x}` is finite with at most `2^L` elements.

**CLASSICAL** (Terras 1976, Böhm–Sontacchi 1978; the backward congruence theorem is from our
notes, in forward form, and is likely folklore).  
-/

namespace Collatz
open CollatzProof

/-- **Shift lemma.** Adding `2^k t` to `n` leaves the first `k` parities (hence `S_k`) unchanged
and shifts `T^k` by `3^{S_k n} t`: `T^k(n + 2^k t) = T^k n + 3^{S_k n} t`. -/
theorem shift_iterate (k : ℕ) : ∀ n t : ℕ,
    oddSteps k (n + 2^k * t) = oddSteps k n ∧
    T^[k] (n + 2^k * t) = T^[k] n + 3 ^ oddSteps k n * t := by
  induction k with
  | zero => intro n t; simp [oddSteps]
  | succ k ih =>
    intro n t
    have e : n + 2^(k+1) * t = n + 2 * (2^k * t) := by ring
    rw [e]
    generalize hs : 2^k * t = s
    have hp : (n + 2 * s) % 2 = n % 2 := by omega
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have hT : T (n + 2 * s) = T n + 2^k * t := by
        simp only [T]; split_ifs <;> omega
      obtain ⟨i1, i2⟩ := ih (T n) t
      refine ⟨?_, ?_⟩
      · simp only [oddSteps]; rw [hT, i1, hp]
      · rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hT, i2]
        simp [oddSteps, h]
    · have hT : T (n + 2 * s) = T n + 2^k * (3 * t) := by
        have : 2^k * (3 * t) = 3 * s := by rw [← hs]; ring
        rw [this]; simp only [T]; split_ifs <;> omega
      obtain ⟨i1, i2⟩ := ih (T n) (3 * t)
      refine ⟨?_, ?_⟩
      · simp only [oddSteps]; rw [hT, i1, hp]
      · rw [Function.iterate_succ_apply, Function.iterate_succ_apply, hT, i2]
        simp only [oddSteps, h, pow_succ]; ring

/-- `S_k(n + 2^k t) = S_k(n)`. -/
theorem oddSteps_shift (k n t : ℕ) : oddSteps k (n + 2^k*t) = oddSteps k n :=
  (shift_iterate k n t).1

/-- `T^k(n + 2^k t) = T^k(n) + 3^{S_k(n)} t`. -/
theorem iterate_shift (k n t : ℕ) : T^[k] (n + 2^k*t) = T^[k] n + 3 ^ oddSteps k n * t :=
  (shift_iterate k n t).2

example : T^[2] 5 = 4 := by decide

/-- `L = 2`: the fixed points `0, 1, 2` of `T^2` have distinct residues mod 4. -/
example : T^[2] 0 = 0 ∧ T^[2] 1 = 1 ∧ T^[2] 2 = 2 ∧ T^[2] 5 ≠ 5 := by decide

/-- **Backward congruence theorem, forward form.** `m` lies in the `T^k`-image of the class
`n + 2^k ℕ` iff `m ≥ T^k n` and `m ≡ T^k n (mod 3^{S_k n})`. -/
theorem image_class_iff (k n m : ℕ) :
    (∃ t, T^[k] (n + 2^k * t) = m) ↔
      (T^[k] n ≤ m ∧ m ≡ T^[k] n [MOD 3 ^ oddSteps k n]) := by
  constructor
  · rintro ⟨t, rfl⟩
    rw [iterate_shift]
    exact ⟨Nat.le_add_right _ _, by
      unfold Nat.ModEq; rw [Nat.add_mul_mod_self_left]⟩
  · rintro ⟨hle, hm⟩
    obtain ⟨c, hc⟩ := (Nat.modEq_iff_dvd' hle).1 hm.symm
    refine ⟨c, ?_⟩
    rw [iterate_shift]; omega

/-- **Difference law.** `n ≡ n' (mod 2^k)` implies `S_k n = S_k n'` and
`T^k n ≡ T^k n' (mod 3^{S_k n})`. -/
theorem backcong_modEq {k n n' : ℕ} (h : n ≡ n' [MOD 2^k]) :
    oddSteps k n = oddSteps k n' ∧ T^[k] n ≡ T^[k] n' [MOD 3 ^ oddSteps k n] := by
  rcases le_total n n' with hle | hle
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).1 h
    have : n' = n + 2^k * t := by omega
    subst this
    rw [oddSteps_shift, iterate_shift]
    refine ⟨rfl, ?_⟩
    unfold Nat.ModEq; rw [Nat.add_mul_mod_self_left]
  · obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).1 h.symm
    have : n = n' + 2^k * t := by omega
    subst this
    rw [oddSteps_shift, iterate_shift]
    refine ⟨rfl, ?_⟩
    unfold Nat.ModEq; rw [Nat.add_mul_mod_self_left]

/-- **Converse of Terras periodicity.** If `n` and `n'` have the same parity vector of length
`k` (`T^i n ≡ T^i n' mod 2` for `i < k`), then `n ≡ n' (mod 2^k)`. -/
theorem modEq_of_parity (k : ℕ) : ∀ {n n' : ℕ},
    (∀ i < k, (T^[i] n) % 2 = (T^[i] n') % 2) → n ≡ n' [MOD 2^k] := by
  induction k with
  | zero => intro n n' _; simp [Nat.modEq_one]
  | succ k ih =>
    intro n n' h
    have h0 : n % 2 = n' % 2 := h 0 (by omega)
    have hT : T n ≡ T n' [MOD 2^k] := ih (fun i hi => by
      have := h (i+1) (by omega)
      rwa [Function.iterate_succ_apply, Function.iterate_succ_apply] at this)
    rw [Nat.modEq_iff_dvd] at hT ⊢
    push_cast at hT ⊢
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have e1 : n = 2 * T n := by simp only [T]; split_ifs; omega
      have e2 : n' = 2 * T n' := by simp only [T]; split_ifs <;> omega
      have : ((n' : ℤ) - n) = 2 * ((T n' : ℤ) - T n) := by omega
      rw [this, pow_succ, mul_comm (2 ^ k : ℤ) 2]
      exact mul_dvd_mul_left 2 hT
    · have e1 : 2 * T n = 3 * n + 1 := by simp only [T]; split_ifs <;> omega
      have e2 : 2 * T n' = 3 * n' + 1 := by simp only [T]; split_ifs <;> omega
      have h3 : (2 ^ (k+1) : ℤ) ∣ 3 * ((n' : ℤ) - n) := by
        have : 3 * ((n' : ℤ) - n) = 2 * ((T n' : ℤ) - T n) := by omega
        rw [this, pow_succ, mul_comm (2 ^ k : ℤ) 2]
        exact mul_dvd_mul_left 2 hT
      have hc : IsCoprime (2 ^ (k+1) : ℤ) 3 := by
        apply IsCoprime.pow_left
        rw [Int.isCoprime_iff_gcd_eq_one]; rfl
      exact hc.dvd_of_dvd_mul_left h3

/-- **Cycle shift.** If `T^L x = x` then `T^L(x + 2^L t) = x + 3^{S_L x} t` for all `t`. -/
theorem cycle_shift {L x : ℕ} (hc : T^[L] x = x) (t : ℕ) :
    T^[L] (x + 2^L * t) = x + 3 ^ oddSteps L x * t := by
  rw [iterate_shift, hc]

/-- Helper for `periodic_unique_mod` in the case `x ≤ y`. -/
theorem periodic_unique_mod_aux {L x y : ℕ} (hL : 0 < L)
    (hx : T^[L] x = x) (hy : T^[L] y = y) (hxy : x ≡ y [MOD 2^L]) (hle : x ≤ y) : x = y := by
  obtain ⟨t, ht⟩ := (Nat.modEq_iff_dvd' hle).1 hxy
  have hy' : y = x + 2^L * t := by omega
  have e := cycle_shift hx t
  rw [← hy', hy] at e
  have e2 : 3 ^ oddSteps L x * t = 2^L * t := by omega
  rcases Nat.eq_zero_or_pos t with h0 | h0
  · subst h0; omega
  · exfalso
    have := Nat.eq_of_mul_eq_mul_right h0 e2
    have h1 := three_pow_mod_two (oddSteps L x)
    obtain ⟨L', rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by omega⟩
    rw [this, pow_succ, Nat.mul_mod_left] at h1
    omega

/-- **Böhm–Sontacchi uniqueness (dynamical form).** For `L > 0`, two fixed points of `T^L`
that are congruent mod `2^L` are equal. -/
theorem periodic_unique_mod {L x y : ℕ} (hL : 0 < L)
    (hx : T^[L] x = x) (hy : T^[L] y = y) (hxy : x ≡ y [MOD 2^L]) : x = y := by
  rcases le_total x y with h | h
  · exact periodic_unique_mod_aux hL hx hy hxy h
  · exact (periodic_unique_mod_aux hL hy hx hxy.symm h).symm

/-- Reduction mod `2^L` is injective on the fixed points of `T^L` (`L > 0`). -/
theorem periodic_injOn_mod {L : ℕ} (hL : 0 < L) :
    Set.InjOn (fun x => x % 2^L) {x | T^[L] x = x} :=
  fun _ hx _ hy hxy => periodic_unique_mod hL hx hy hxy

/-- **Counting.** For `L > 0`, `{x | T^L x = x}` is finite and has at most `2^L` elements. -/
theorem periodic_ncard_le {L : ℕ} (hL : 0 < L) :
    {x | T^[L] x = x}.Finite ∧ {x | T^[L] x = x}.ncard ≤ 2^L := by
  have hmaps : Set.MapsTo (fun x => x % 2^L) {x | T^[L] x = x} (↑(Finset.range (2^L))) :=
    fun x _ => by simp [Nat.mod_lt x (by positivity : 0 < 2^L)]
  have hfin : {x | T^[L] x = x}.Finite :=
    Set.Finite.of_finite_image ((Finset.range (2^L)).finite_toSet.subset
      (Set.mapsTo_iff_image_subset.1 hmaps)) (periodic_injOn_mod hL)
  refine ⟨hfin, ?_⟩
  have := Set.ncard_le_ncard_of_injOn _ hmaps (periodic_injOn_mod hL)
  rwa [Set.ncard_coe_finset, Finset.card_range] at this

#print axioms shift_iterate
#print axioms oddSteps_shift
#print axioms iterate_shift
#print axioms image_class_iff
#print axioms backcong_modEq
#print axioms modEq_of_parity
#print axioms cycle_shift
#print axioms periodic_unique_mod
#print axioms periodic_injOn_mod
#print axioms periodic_ncard_le

end Collatz
