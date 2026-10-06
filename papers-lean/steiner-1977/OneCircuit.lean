import OddStepBound

/-!
# Steiner 1-circuits in a finite range

A *1-circuit* is a `T`-cycle whose parity vector is one run of `k` odd steps followed by one
run of `l` even steps.  We prove the elementary Steiner reduction:

* odd run: `2^k (T^k x + 1) = 3^k (x + 1)`; even run: `2^l T^l y = y`;
* circuit equation: `m + 1 = 2^k a` with `a (2^{k+l} - 3^k) = 2^l - 1`;
  (in Lean this is stated subtraction-free, `one_circuit_eq`: `a 2^{k+l} + 1 = a 3^k + 2^l`; the
  two forms are equivalent because `3^k < 2^{k+l}` and `2^l ≥ 1`, see `one_circuit_size`);
* hence `2^{k+l-1} < 3^k < 2^{k+l}` (so `l` is determined by `k`) and
  `(2^{k+l} - 3^k) ∣ 2^l - 1`;

Remark: the divisibility clause of `circOK` is redundant in practice: for every
tested `k ≥ 2` (Python, `2 ≤ k ≤ 20000`, and a further check up to `10^5`),
`2^L - 3^k > 2^{L-k} - 1`, so the certificate really checks a size
(Diophantine-approximation) fact about `log₂ 3`.  Extending the range beyond `10^5` is a dead end.

We then exclude every nontrivial 1-circuit with `k < 100000` by a kernel-checked
certificate (`decide +kernel`, no `native_decide`, no `set_option`).  Soundness of the
certificate does not depend on the accuracy of `candL` (a rational approximation of `log₂ 3`).

Steiner (1977) proved that there is **no** nontrivial 1-circuit at all, and Simons (2005)
extended this; both use Baker/Rhin-type linear-form bounds, which are not formalized here.
This file is a finite-range formal instance (`k < 100000`) of Steiner's theorem; it does not
address general cycles.
-/

namespace Collatz
open CollatzProof

/-- `(m,k,l)` is a 1-circuit: `k ≥ 1` odd steps, then `l ≥ 1` even steps, returning to `m`. -/
def IsOneCircuit (m k l : ℕ) : Prop :=
  1 ≤ k ∧ 1 ≤ l ∧ (∀ i < k, T^[i] m % 2 = 1) ∧ (∀ i < l, T^[k+i] m % 2 = 0) ∧ T^[k+l] m = m

/-- For odd `x`, `2 T x = 3x + 1`. -/
theorem two_mul_T_odd {x : ℕ} (h : x % 2 = 1) : 2 * T x = 3 * x + 1 := by
  simp only [T, show x % 2 ≠ 0 by omega, ite_false]; omega

/-- For even `x`, `2 T x = x`. -/
theorem two_mul_T_even {x : ℕ} (h : x % 2 = 0) : 2 * T x = x := by
  simp only [T, h, ite_true]; omega

/-- **Odd run.** If `T^i x` is odd for all `i < k`, then `2^k (T^k x + 1) = 3^k (x + 1)`. -/
theorem odd_run (k x : ℕ) (h : ∀ i < k, T^[i] x % 2 = 1) :
    2 ^ k * (T^[k] x + 1) = 3 ^ k * (x + 1) := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    have h0 : x % 2 = 1 := h 0 (by omega)
    have ih' := ih (T x) (fun i hi => by
      have := h (i + 1) (by omega); rwa [Function.iterate_succ_apply] at this)
    have h2 := two_mul_T_odd h0
    rw [Function.iterate_succ_apply, pow_succ, pow_succ]
    calc 2 ^ k * 2 * (T^[k] (T x) + 1) = 2 * (2 ^ k * (T^[k] (T x) + 1)) := by ring
      _ = 2 * (3 ^ k * (T x + 1)) := by rw [ih']
      _ = 3 ^ k * (2 * T x + 2) := by ring
      _ = 3 ^ k * 3 * (x + 1) := by rw [h2]; ring

/-- **Even run.** If `T^i y` is even for all `i < l`, then `2^l T^l y = y`. -/
theorem even_run (l y : ℕ) (h : ∀ i < l, T^[i] y % 2 = 0) : 2 ^ l * T^[l] y = y := by
  induction l generalizing y with
  | zero => simp
  | succ l ih =>
    have h0 : y % 2 = 0 := h 0 (by omega)
    have ih' := ih (T y) (fun i hi => by
      have := h (i + 1) (by omega); rwa [Function.iterate_succ_apply] at this)
    have h2 := two_mul_T_even h0
    rw [Function.iterate_succ_apply, pow_succ]
    calc 2 ^ l * 2 * T^[l] (T y) = 2 * (2 ^ l * T^[l] (T y)) := by ring
      _ = y := by rw [ih', h2]

/-- **Circuit equation.** A 1-circuit has `a ≥ 1` with `m+1 = 2^k a` and
`a 2^{k+l} + 1 = a 3^k + 2^l`. -/
theorem one_circuit_eq {m k l : ℕ} (h : IsOneCircuit m k l) :
    ∃ a, 1 ≤ a ∧ m + 1 = 2 ^ k * a ∧ a * 2 ^ (k + l) + 1 = a * 3 ^ k + 2 ^ l := by
  obtain ⟨hk, hl, hodd, heven, hper⟩ := h
  have hA := odd_run k m hodd
  set x := T^[k] m with hx
  have hB := even_run l x (fun i hi => by
    rw [hx, ← Function.iterate_add_apply, add_comm]; exact heven i hi)
  have hxl : T^[l] x = m := by
    rw [hx, ← Function.iterate_add_apply, add_comm]; exact hper
  rw [hxl] at hB
  have hcop : Nat.Coprime (2 ^ k) (3 ^ k) := Nat.Coprime.pow k k (by norm_num)
  have hdvd : 2 ^ k ∣ m + 1 :=
    hcop.dvd_of_dvd_mul_left ⟨x + 1, by rw [← hA]⟩
  obtain ⟨a, ha⟩ := hdvd
  have hpos : 0 < 2 ^ k := by positivity
  have hx1 : x + 1 = 3 ^ k * a := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [hA, ha]; ring
  refine ⟨a, ?_, ha, ?_⟩
  · rcases Nat.eq_zero_or_pos a with h0 | h0
    · rw [h0] at ha; omega
    · exact h0
  · rw [pow_add]
    have : a * (2 ^ k * 2 ^ l) = 2 ^ l * (m + 1) := by rw [ha]; ring
    rw [this]
    nlinarith [hB, hx1]

/-- **Size and divisibility.** For a 1-circuit, `2^{k+l-1} < 3^k < 2^{k+l}` and
`(2^{k+l} - 3^k) ∣ 2^l - 1`. -/
theorem one_circuit_size {m k l : ℕ} (h : IsOneCircuit m k l) :
    2 ^ (k + l - 1) < 3 ^ k ∧ 3 ^ k < 2 ^ (k + l) ∧ (2 ^ l - 1) % (2 ^ (k + l) - 3 ^ k) = 0 := by
  obtain ⟨a, ha, -, E⟩ := one_circuit_eq h
  obtain ⟨hk, hl, -⟩ := h
  have h2l : 2 ≤ 2 ^ l := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ l := Nat.pow_le_pow_right (by norm_num) hl
  have hi : 3 ^ k < 2 ^ (k + l) := by
    have : a * 3 ^ k < a * 2 ^ (k + l) := by omega
    exact Nat.lt_of_mul_lt_mul_left this
  have hii : 2 ^ (k + l) + 1 ≤ 3 ^ k + 2 ^ l := by
    obtain ⟨b, rfl⟩ : ∃ b, a = b + 1 := ⟨a - 1, by omega⟩
    have := Nat.mul_le_mul_left b (le_of_lt hi)
    nlinarith [E, this]
  refine ⟨?_, hi, ?_⟩
  · have h1 : 2 ^ l ≤ 2 ^ (k + l - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 2 ^ (k + l) = 2 * 2 ^ (k + l - 1) := by
      rw [show k + l = (k + l - 1) + 1 by omega, pow_succ]; simp; ring
    omega
  · obtain ⟨D, hD⟩ : ∃ D, 2 ^ (k + l) = D + 3 ^ k := ⟨2 ^ (k + l) - 3 ^ k, by omega⟩
    have hD' : 2 ^ (k + l) - 3 ^ k = D := by omega
    rw [hD'] at *
    rw [hD] at E
    have : 2 ^ l - 1 = a * D := by
      have : a * (D + 3 ^ k) = a * D + a * 3 ^ k := by ring
      omega
    rw [this]; exact Nat.mul_mod_left a D

/-- Uniqueness of the exponent `L` with `2^{L-1} < 3^k < 2^L`. -/
theorem exp_unique {k c L : ℕ} (hc1 : 2 ^ (c - 1) ≤ 3 ^ k) (hc2 : 3 ^ k < 2 ^ c) (hc : 1 ≤ c)
    (hL1 : 2 ^ (L - 1) < 3 ^ k) (hL2 : 3 ^ k < 2 ^ L) : c = L := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have : 2 ^ c ≤ 2 ^ (L - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have : 2 ^ L ≤ 2 ^ (c - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

/-- Kernel-checkable certificate for one `k`: `candL k` is the exponent `L` with
`2^{L-1} ≤ 3^k < 2^L`, and `(2^L - 3^k) ∤ 2^{L-k} - 1`. -/
def circOK (k : ℕ) : Bool :=
  Nat.ble (2 ^ (candL k - 1)) (3 ^ k) && Nat.blt (3 ^ k) (2 ^ candL k) && Nat.blt k (candL k) &&
  ((2 ^ (candL k - k) - 1) % (2 ^ candL k - 3 ^ k) != 0)

/-- If `circOK k` holds, there is no 1-circuit with `k` odd steps. -/
theorem circOK_sound {m k l : ℕ} (h : IsOneCircuit m k l) (hk : circOK k = true) : False := by
  obtain ⟨s1, s2, s3⟩ := one_circuit_size h
  simp only [circOK, Bool.and_eq_true, Nat.ble_eq, Nat.blt_eq, bne_iff_ne, ne_eq] at hk
  obtain ⟨⟨⟨c1, c2⟩, c3⟩, c4⟩ := hk
  have hc : 1 ≤ candL k := by unfold candL; omega
  have e := exp_unique c1 c2 hc s1 s2
  rw [e, show k + l - k = l by omega] at c4
  exact c4 s3

/-- `circRange lo n` checks `circOK k` for `lo ≤ k < lo + n`. -/
def circRange (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => circRange lo n && circOK (lo + n)

theorem circRange_sound (lo : ℕ) : ∀ n, circRange lo n = true → ∀ k, lo ≤ k → k < lo + n →
    circOK k = true := by
  intro n
  induction n with
  | zero => intro _ k h1 h2; omega
  | succ n ih =>
    intro h k h1 h2
    simp only [circRange, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge k (lo + n) with hk | hk
    · exact ih h.1 k h1 hk
    · have : k = lo + n := by omega
      subst this; exact h.2


/-- `CircRange lo hi`: `circOK k` holds for all `lo ≤ k < hi`. -/
def CircRange (lo hi : ℕ) : Prop := ∀ k, lo ≤ k → k < hi → circOK k = true

theorem circRange_nil (hi : ℕ) : CircRange hi hi := fun k h1 h2 => absurd h2 (by omega)

theorem circRange_cons {lo n hi : ℕ} (h : circRange lo n = true) (hr : CircRange (lo + n) hi) :
    CircRange lo hi := fun k h1 h2 => by
  rcases Nat.lt_or_ge k (lo + n) with hk | hk
  · exact circRange_sound lo n h k h1 hk
  · exact hr k hk h2

theorem circBlock_0 : circRange 2 998 = true := by decide +kernel
theorem circBlock_1 : circRange 1000 1000 = true := by decide +kernel
theorem circBlock_2 : circRange 2000 1000 = true := by decide +kernel
theorem circBlock_3 : circRange 3000 1000 = true := by decide +kernel
theorem circBlock_4 : circRange 4000 1000 = true := by decide +kernel
theorem circBlock_5 : circRange 5000 1000 = true := by decide +kernel
theorem circBlock_6 : circRange 6000 1000 = true := by decide +kernel
theorem circBlock_7 : circRange 7000 1000 = true := by decide +kernel
theorem circBlock_8 : circRange 8000 1000 = true := by decide +kernel
theorem circBlock_9 : circRange 9000 1000 = true := by decide +kernel
theorem circBlock_10 : circRange 10000 1000 = true := by decide +kernel
theorem circBlock_11 : circRange 11000 1000 = true := by decide +kernel
theorem circBlock_12 : circRange 12000 1000 = true := by decide +kernel
theorem circBlock_13 : circRange 13000 1000 = true := by decide +kernel
theorem circBlock_14 : circRange 14000 1000 = true := by decide +kernel
theorem circBlock_15 : circRange 15000 1000 = true := by decide +kernel
theorem circBlock_16 : circRange 16000 1000 = true := by decide +kernel
theorem circBlock_17 : circRange 17000 1000 = true := by decide +kernel
theorem circBlock_18 : circRange 18000 1000 = true := by decide +kernel
theorem circBlock_19 : circRange 19000 1000 = true := by decide +kernel
theorem circBlock_20 : circRange 20000 1000 = true := by decide +kernel
theorem circBlock_21 : circRange 21000 1000 = true := by decide +kernel
theorem circBlock_22 : circRange 22000 1000 = true := by decide +kernel
theorem circBlock_23 : circRange 23000 1000 = true := by decide +kernel
theorem circBlock_24 : circRange 24000 1000 = true := by decide +kernel
theorem circBlock_25 : circRange 25000 1000 = true := by decide +kernel
theorem circBlock_26 : circRange 26000 1000 = true := by decide +kernel
theorem circBlock_27 : circRange 27000 1000 = true := by decide +kernel
theorem circBlock_28 : circRange 28000 1000 = true := by decide +kernel
theorem circBlock_29 : circRange 29000 1000 = true := by decide +kernel
theorem circBlock_30 : circRange 30000 1000 = true := by decide +kernel
theorem circBlock_31 : circRange 31000 1000 = true := by decide +kernel
theorem circBlock_32 : circRange 32000 1000 = true := by decide +kernel
theorem circBlock_33 : circRange 33000 1000 = true := by decide +kernel
theorem circBlock_34 : circRange 34000 1000 = true := by decide +kernel
theorem circBlock_35 : circRange 35000 1000 = true := by decide +kernel
theorem circBlock_36 : circRange 36000 1000 = true := by decide +kernel
theorem circBlock_37 : circRange 37000 1000 = true := by decide +kernel
theorem circBlock_38 : circRange 38000 1000 = true := by decide +kernel
theorem circBlock_39 : circRange 39000 1000 = true := by decide +kernel
theorem circBlock_40 : circRange 40000 1000 = true := by decide +kernel
theorem circBlock_41 : circRange 41000 1000 = true := by decide +kernel
theorem circBlock_42 : circRange 42000 1000 = true := by decide +kernel
theorem circBlock_43 : circRange 43000 1000 = true := by decide +kernel
theorem circBlock_44 : circRange 44000 1000 = true := by decide +kernel
theorem circBlock_45 : circRange 45000 1000 = true := by decide +kernel
theorem circBlock_46 : circRange 46000 1000 = true := by decide +kernel
theorem circBlock_47 : circRange 47000 1000 = true := by decide +kernel
theorem circBlock_48 : circRange 48000 1000 = true := by decide +kernel
theorem circBlock_49 : circRange 49000 1000 = true := by decide +kernel
theorem circBlock_50 : circRange 50000 1000 = true := by decide +kernel
theorem circBlock_51 : circRange 51000 1000 = true := by decide +kernel
theorem circBlock_52 : circRange 52000 1000 = true := by decide +kernel
theorem circBlock_53 : circRange 53000 1000 = true := by decide +kernel
theorem circBlock_54 : circRange 54000 1000 = true := by decide +kernel
theorem circBlock_55 : circRange 55000 1000 = true := by decide +kernel
theorem circBlock_56 : circRange 56000 1000 = true := by decide +kernel
theorem circBlock_57 : circRange 57000 1000 = true := by decide +kernel
theorem circBlock_58 : circRange 58000 1000 = true := by decide +kernel
theorem circBlock_59 : circRange 59000 1000 = true := by decide +kernel
theorem circBlock_60 : circRange 60000 1000 = true := by decide +kernel
theorem circBlock_61 : circRange 61000 1000 = true := by decide +kernel
theorem circBlock_62 : circRange 62000 1000 = true := by decide +kernel
theorem circBlock_63 : circRange 63000 1000 = true := by decide +kernel
theorem circBlock_64 : circRange 64000 1000 = true := by decide +kernel
theorem circBlock_65 : circRange 65000 1000 = true := by decide +kernel
theorem circBlock_66 : circRange 66000 1000 = true := by decide +kernel
theorem circBlock_67 : circRange 67000 1000 = true := by decide +kernel
theorem circBlock_68 : circRange 68000 1000 = true := by decide +kernel
theorem circBlock_69 : circRange 69000 1000 = true := by decide +kernel
theorem circBlock_70 : circRange 70000 1000 = true := by decide +kernel
theorem circBlock_71 : circRange 71000 1000 = true := by decide +kernel
theorem circBlock_72 : circRange 72000 1000 = true := by decide +kernel
theorem circBlock_73 : circRange 73000 1000 = true := by decide +kernel
theorem circBlock_74 : circRange 74000 1000 = true := by decide +kernel
theorem circBlock_75 : circRange 75000 1000 = true := by decide +kernel
theorem circBlock_76 : circRange 76000 1000 = true := by decide +kernel
theorem circBlock_77 : circRange 77000 1000 = true := by decide +kernel
theorem circBlock_78 : circRange 78000 1000 = true := by decide +kernel
theorem circBlock_79 : circRange 79000 1000 = true := by decide +kernel
theorem circBlock_80 : circRange 80000 1000 = true := by decide +kernel
theorem circBlock_81 : circRange 81000 1000 = true := by decide +kernel
theorem circBlock_82 : circRange 82000 1000 = true := by decide +kernel
theorem circBlock_83 : circRange 83000 1000 = true := by decide +kernel
theorem circBlock_84 : circRange 84000 1000 = true := by decide +kernel
theorem circBlock_85 : circRange 85000 1000 = true := by decide +kernel
theorem circBlock_86 : circRange 86000 1000 = true := by decide +kernel
theorem circBlock_87 : circRange 87000 1000 = true := by decide +kernel
theorem circBlock_88 : circRange 88000 1000 = true := by decide +kernel
theorem circBlock_89 : circRange 89000 1000 = true := by decide +kernel
theorem circBlock_90 : circRange 90000 1000 = true := by decide +kernel
theorem circBlock_91 : circRange 91000 1000 = true := by decide +kernel
theorem circBlock_92 : circRange 92000 1000 = true := by decide +kernel
theorem circBlock_93 : circRange 93000 1000 = true := by decide +kernel
theorem circBlock_94 : circRange 94000 1000 = true := by decide +kernel
theorem circBlock_95 : circRange 95000 1000 = true := by decide +kernel
theorem circBlock_96 : circRange 96000 1000 = true := by decide +kernel
theorem circBlock_97 : circRange 97000 1000 = true := by decide +kernel
theorem circBlock_98 : circRange 98000 1000 = true := by decide +kernel
theorem circBlock_99 : circRange 99000 1000 = true := by decide +kernel

/-- Kernel-verified: `circOK k` for all `2 ≤ k < 100000`. -/
theorem circRange_2_100000 : CircRange 2 100000 :=
  circRange_cons circBlock_0 (circRange_cons circBlock_1 (circRange_cons circBlock_2 (circRange_cons circBlock_3 (circRange_cons circBlock_4 (circRange_cons circBlock_5 (circRange_cons circBlock_6 (circRange_cons circBlock_7 (circRange_cons circBlock_8 (circRange_cons circBlock_9 (circRange_cons circBlock_10 (circRange_cons circBlock_11 (circRange_cons circBlock_12 (circRange_cons circBlock_13 (circRange_cons circBlock_14 (circRange_cons circBlock_15 (circRange_cons circBlock_16 (circRange_cons circBlock_17 (circRange_cons circBlock_18 (circRange_cons circBlock_19 (circRange_cons circBlock_20 (circRange_cons circBlock_21 (circRange_cons circBlock_22 (circRange_cons circBlock_23 (circRange_cons circBlock_24 (circRange_cons circBlock_25 (circRange_cons circBlock_26 (circRange_cons circBlock_27 (circRange_cons circBlock_28 (circRange_cons circBlock_29 (circRange_cons circBlock_30 (circRange_cons circBlock_31 (circRange_cons circBlock_32 (circRange_cons circBlock_33 (circRange_cons circBlock_34 (circRange_cons circBlock_35 (circRange_cons circBlock_36 (circRange_cons circBlock_37 (circRange_cons circBlock_38 (circRange_cons circBlock_39 (circRange_cons circBlock_40 (circRange_cons circBlock_41 (circRange_cons circBlock_42 (circRange_cons circBlock_43 (circRange_cons circBlock_44 (circRange_cons circBlock_45 (circRange_cons circBlock_46 (circRange_cons circBlock_47 (circRange_cons circBlock_48 (circRange_cons circBlock_49 (circRange_cons circBlock_50 (circRange_cons circBlock_51 (circRange_cons circBlock_52 (circRange_cons circBlock_53 (circRange_cons circBlock_54 (circRange_cons circBlock_55 (circRange_cons circBlock_56 (circRange_cons circBlock_57 (circRange_cons circBlock_58 (circRange_cons circBlock_59 (circRange_cons circBlock_60 (circRange_cons circBlock_61 (circRange_cons circBlock_62 (circRange_cons circBlock_63 (circRange_cons circBlock_64 (circRange_cons circBlock_65 (circRange_cons circBlock_66 (circRange_cons circBlock_67 (circRange_cons circBlock_68 (circRange_cons circBlock_69 (circRange_cons circBlock_70 (circRange_cons circBlock_71 (circRange_cons circBlock_72 (circRange_cons circBlock_73 (circRange_cons circBlock_74 (circRange_cons circBlock_75 (circRange_cons circBlock_76 (circRange_cons circBlock_77 (circRange_cons circBlock_78 (circRange_cons circBlock_79 (circRange_cons circBlock_80 (circRange_cons circBlock_81 (circRange_cons circBlock_82 (circRange_cons circBlock_83 (circRange_cons circBlock_84 (circRange_cons circBlock_85 (circRange_cons circBlock_86 (circRange_cons circBlock_87 (circRange_cons circBlock_88 (circRange_cons circBlock_89 (circRange_cons circBlock_90 (circRange_cons circBlock_91 (circRange_cons circBlock_92 (circRange_cons circBlock_93 (circRange_cons circBlock_94 (circRange_cons circBlock_95 (circRange_cons circBlock_96 (circRange_cons circBlock_97 (circRange_cons circBlock_98 (circRange_cons circBlock_99 (circRange_nil 100000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- **Main result.** Every 1-circuit with fewer than `100000` odd steps is the trivial one, `m = 1`. -/
theorem one_circuit_eq_one {m k l : ℕ} (h : IsOneCircuit m k l) (hk : k < 100000) : m = 1 := by
  rcases Nat.lt_or_ge k 2 with hk2 | hk2
  · have hk1 : k = 1 := by have := h.1; omega
    subst hk1
    obtain ⟨s1, s2, -⟩ := one_circuit_size h
    have e := exp_unique (c := 2) (k := 1) (by norm_num) (by norm_num) (by norm_num) s1 s2
    have hl : l = 1 := by omega
    subst hl
    obtain ⟨a, -, ha, E⟩ := one_circuit_eq h
    norm_num at ha E
    omega
  · exact (circOK_sound h (circRange_2_100000 k hk2 hk)).elim

/-- Contrapositive: a 1-circuit with `m > 1` has at least `100000` odd steps. -/
theorem one_circuit_k_ge {m k l : ℕ} (h : IsOneCircuit m k l) (hm : 1 < m) : 100000 ≤ k := by
  by_contra hc
  have := one_circuit_eq_one h (by omega)
  omega

/-- Non-vacuity: the trivial cycle `1 → 2 → 1` is a 1-circuit with `k = l = 1`. -/
example : IsOneCircuit 1 1 1 := by
  refine ⟨le_rfl, le_rfl, ?_, ?_, ?_⟩
  · intro i hi; interval_cases i; decide
  · intro i hi; interval_cases i; decide
  · decide

end Collatz

#print axioms Collatz.odd_run
#print axioms Collatz.even_run
#print axioms Collatz.one_circuit_eq
#print axioms Collatz.one_circuit_size
#print axioms Collatz.exp_unique
#print axioms Collatz.circOK_sound
#print axioms Collatz.circRange_2_100000
#print axioms Collatz.one_circuit_eq_one
#print axioms Collatz.one_circuit_k_ge
