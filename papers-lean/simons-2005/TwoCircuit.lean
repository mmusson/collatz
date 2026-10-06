import OneCircuit
import Collatz.CycleMin

/-!
# Simons-type 2-circuits in a finite range

A *2-circuit* `IsTwoCircuit m k1 l1 k2 l2` is a `T`-cycle through `m` whose parity vector is
`k1 ≥ 1` odd steps, `l1 ≥ 1` even steps, `k2 ≥ 1` odd steps, `l2 ≥ 1` even steps.  With
`L = k1+l1+k2+l2`, `k = k1+k2`:

* `two_circuit_oddSteps`: `S_L(m) = k`;
* `two_circuit_eq` (2-circuit equation, subtraction-free):
  `2^L m + 2^{k1+k2+l1} + 3^{k2} 2^{k1} = 3^k m + 3^k + 3^{k2} 2^{k1+l1}`;
* `two_circuit_dvd`: `2^{k1} ∣ m + 1`;  `two_circuit_rotate`: rotating by one odd+even block
  gives the 2-circuit `(T^{k1+l1} m, k2, l2, k1, l1)`;
* `two_circuit_size` (for `k2 ≤ k1`): `2^L 2^{k+1} < 2^{k+1} 3^k + 2^L (2^{⌊k/2⌋+1} + 3^{⌊k/2⌋})`,
  a split-independent size inequality;
* `twoOK k` is an `O(1)`-per-`k` kernel certificate refuting that inequality (sound regardless of
  the accuracy of `candL`), checked by `decide +kernel` for all `11 ≤ k < 100000`
  (it fails exactly for `k ∈ {1,2,3,4,5,6,8,10}`, per a Python check);
* the small `k` are covered by `oddSteps_ge_of_cycle` (`k ≥ 971`), giving
  `two_circuit_eq_one`: **every 2-circuit with `k1+k2 < 100000` has `m = 1`**.
* Length corollaries: nontrivial 1- and 2-circuits have `L ≥ 158497`.

Finite-range instance of Simons (2005), who proved there are **no** nontrivial 2-cycles, using
Baker-type linear-form bounds (not formalized here).  It does not address general cycles.
-/

namespace Collatz
open CollatzProof

/-- `(m,k1,l1,k2,l2)` is a 2-circuit: runs of `k1` odd, `l1` even, `k2` odd, `l2` even steps
(all `≥ 1`), then back to `m`.  No minimal period is required: `IsTwoCircuit 1 1 1 1 1` is the
trivial cycle traversed twice. -/
def IsTwoCircuit (m k1 l1 k2 l2 : ℕ) : Prop :=
  1 ≤ k1 ∧ 1 ≤ l1 ∧ 1 ≤ k2 ∧ 1 ≤ l2 ∧ (∀ i < k1, T^[i] m % 2 = 1) ∧
    (∀ i < l1, T^[k1+i] m % 2 = 0) ∧ (∀ i < k2, T^[k1+l1+i] m % 2 = 1) ∧
    (∀ i < l2, T^[k1+l1+k2+i] m % 2 = 0) ∧ T^[k1+l1+k2+l2] m = m

/-- `T^i (T^a m) = T^{a+i} m`. -/
theorem iter_shift (a i m : ℕ) : T^[i] (T^[a] m) = T^[a+i] m := by
  rw [← Function.iterate_add_apply, add_comm]

/-- A run of `k` odd values contributes `k` odd steps. -/
theorem oddSteps_odd_run (k x : ℕ) (h : ∀ i < k, T^[i] x % 2 = 1) : oddSteps k x = k := by
  induction k generalizing x with
  | zero => rfl
  | succ k ih =>
    have h0 : x % 2 = 1 := h 0 (by omega)
    have ih' := ih (T x) (fun i hi => by
      have := h (i + 1) (by omega); rwa [Function.iterate_succ_apply] at this)
    simp only [oddSteps, ih', h0]

/-- A run of `l` even values contributes no odd steps. -/
theorem oddSteps_even_run (l y : ℕ) (h : ∀ i < l, T^[i] y % 2 = 0) : oddSteps l y = 0 := by
  induction l generalizing y with
  | zero => rfl
  | succ l ih =>
    have h0 : y % 2 = 0 := h 0 (by omega)
    have ih' := ih (T y) (fun i hi => by
      have := h (i + 1) (by omega); rwa [Function.iterate_succ_apply] at this)
    simp only [oddSteps, ih', h0]

/-- A 2-circuit has exactly `k1 + k2` odd steps per period. -/
theorem two_circuit_oddSteps {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) :
    oddSteps (k1+l1+k2+l2) m = k1 + k2 := by
  obtain ⟨-, -, -, -, h1, h2, h3, h4, -⟩ := h
  rw [oddSteps_add, oddSteps_add, oddSteps_add]
  rw [oddSteps_odd_run k1 m h1,
    oddSteps_even_run l1 _ (fun i hi => by rw [iter_shift]; exact h2 i hi),
    oddSteps_odd_run k2 _ (fun i hi => by rw [iter_shift]; exact h3 i hi),
    oddSteps_even_run l2 _ (fun i hi => by rw [iter_shift]; exact h4 i hi)]
  omega

/-- **2-circuit equation** (subtraction-free form). -/
theorem two_circuit_eq {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) :
    2^(k1+l1+k2+l2)*m + 2^(k1+k2+l1) + 3^k2*2^k1 =
      3^(k1+k2)*m + 3^(k1+k2) + 3^k2*2^(k1+l1) := by
  obtain ⟨-, -, -, -, h1, h2, h3, h4, hper⟩ := h
  have hA := odd_run k1 m h1
  have hB := even_run l1 (T^[k1] m) (fun i hi => by rw [iter_shift]; exact h2 i hi)
  have hC := odd_run k2 (T^[k1+l1] m) (fun i hi => by rw [iter_shift]; exact h3 i hi)
  have hD := even_run l2 (T^[k1+l1+k2] m) (fun i hi => by rw [iter_shift]; exact h4 i hi)
  rw [iter_shift] at hB hC hD
  rw [hper] at hD
  generalize T^[k1] m = x1 at *
  generalize T^[k1+l1] m = y at *
  generalize T^[k1+l1+k2] m = x2 at *
  have hA' : (2:ℤ)^k1 * ((x1:ℤ)+1) = 3^k1 * ((m:ℤ)+1) := by exact_mod_cast hA
  have hB' : (2:ℤ)^l1 * (y:ℤ) = x1 := by exact_mod_cast hB
  have hC' : (2:ℤ)^k2 * ((x2:ℤ)+1) = 3^k2 * ((y:ℤ)+1) := by exact_mod_cast hC
  have hD' : (2:ℤ)^l2 * (m:ℤ) = x2 := by exact_mod_cast hD
  have : (2:ℤ)^(k1+l1+k2+l2)*m + 2^(k1+k2+l1) + 3^k2*2^k1 =
      3^(k1+k2)*m + 3^(k1+k2) + 3^k2*2^(k1+l1) := by
    simp only [pow_add]
    linear_combination (3:ℤ)^k2 * hA' + (2:ℤ)^k1 * 3^k2 * hB' + (2:ℤ)^k1 * 2^l1 * hC'
      + (2:ℤ)^k1 * 2^l1 * 2^k2 * hD'
  exact_mod_cast this

/-- `2^{k1}` divides `m + 1`. -/
theorem two_circuit_dvd {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) : 2^k1 ∣ m + 1 := by
  have hA := odd_run k1 m h.2.2.2.2.1
  have hcop : Nat.Coprime (2 ^ k1) (3 ^ k1) := Nat.Coprime.pow k1 k1 (by norm_num)
  exact hcop.dvd_of_dvd_mul_left ⟨_, hA.symm⟩

/-- `T^L m = m ⇒ T^{c+L} m = T^c m`. -/
theorem iter_period {m L : ℕ} (h : T^[L] m = m) (c : ℕ) : T^[c + L] m = T^[c] m := by
  rw [Function.iterate_add_apply, h]

/-- **Rotation.** Starting at the second odd block gives again a 2-circuit, with blocks swapped. -/
theorem two_circuit_rotate {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) :
    IsTwoCircuit (T^[k1+l1] m) k2 l2 k1 l1 := by
  obtain ⟨g1, g2, g3, g4, h1, h2, h3, h4, hper⟩ := h
  refine ⟨g3, g4, g1, g2, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, fun i hi => ?_, ?_⟩
  · rw [iter_shift]; exact h3 i hi
  · rw [iter_shift, show k1 + l1 + (k2 + i) = k1 + l1 + k2 + i by omega]; exact h4 i hi
  · rw [iter_shift, show k1 + l1 + (k2 + l2 + i) = i + (k1 + l1 + k2 + l2) by omega,
      iter_period hper]; exact h1 i hi
  · rw [iter_shift, show k1 + l1 + (k2 + l2 + k1 + i) = (k1 + i) + (k1 + l1 + k2 + l2) by omega,
      iter_period hper]; exact h2 i hi
  · rw [iter_shift, show k1 + l1 + (k2 + l2 + k1 + l1) = (k1 + l1) + (k1 + l1 + k2 + l2) by omega,
      iter_period hper]

/-- The starting point of a 2-circuit is odd. -/
theorem two_circuit_odd {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) : m % 2 = 1 :=
  h.2.2.2.2.1 0 (by have := h.1; omega)

/-- **Size inequality** (for `k2 ≤ k1`), with `L = k1+l1+k2+l2`, `k = k1+k2`:
`2^L 2^{k+1} < 2^{k+1} 3^k + 2^L (2^{⌊k/2⌋+1} + 3^{⌊k/2⌋})`. -/
theorem two_circuit_size {m k1 l1 k2 l2 : ℕ} (hk : k2 ≤ k1) (h : IsTwoCircuit m k1 l1 k2 l2) :
    2^(k1+l1+k2+l2) * 2^(k1+k2+1) < 2^(k1+k2+1) * 3^(k1+k2) +
      2^(k1+l1+k2+l2) * (2^((k1+k2)/2+1) + 3^((k1+k2)/2)) := by
  have hodd := two_circuit_odd h
  have hL : 0 < k1+l1+k2+l2 := by have := h.1; omega
  have H3 := three_pow_lt_two_pow_of_cycle (by omega) hL h.2.2.2.2.2.2.2.2
  rw [two_circuit_oddSteps h] at H3
  have E := two_circuit_eq h
  obtain ⟨r, hr⟩ := two_circuit_dvd h
  have hl2 := h.2.2.2.1
  set N := 2^(k1+l1+k2+l2) with hN
  set K := 3^(k1+k2) with hK
  set a := 2^k1 with ha
  set q := 3^k2 with hq
  have hB : 1 ≤ 2^(k1+k2+l1) := Nat.one_le_two_pow
  have hr1 : 1 ≤ r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0] at hr; omega
    · exact h0
  have hab : 2^(k1+l1) = a * 2^l1 := by rw [ha, pow_add]
  -- (**)  N a < K a + N + q (a 2^l1)
  have hstar : N * a < K * a + N + q * 2^(k1+l1) := by
    have e1 : N * (m + 1) < K * (m + 1) + N + q * 2^(k1+l1) := by nlinarith
    rw [hr] at e1
    obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
    have : K * (a * s) ≤ N * (a * s) := Nat.mul_le_mul_right _ H3.le
    nlinarith
  set c := 2^(k2+1) with hc
  have hmul := Nat.mul_lt_mul_of_pos_right hstar (show 0 < c by positivity)
  have hac : a * c = 2^(k1+k2+1) := by rw [ha, hc, ← pow_add]; ring_nf
  have habc : 2^(k1+l1) * c ≤ N := by
    rw [hc, hN, ← pow_add]; exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have hc2 : c ≤ 2^((k1+k2)/2+1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hq2 : q ≤ 3^((k1+k2)/2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have t1 : q * 2^(k1+l1) * c ≤ N * q := by
    calc q * 2^(k1+l1) * c = q * (2^(k1+l1) * c) := by ring
      _ ≤ q * N := Nat.mul_le_mul_left _ habc
      _ = N * q := by ring
  have t2 : N * c ≤ N * 2^((k1+k2)/2+1) := Nat.mul_le_mul_left _ hc2
  have t3 : N * q ≤ N * 3^((k1+k2)/2) := Nat.mul_le_mul_left _ hq2
  have e2 : N * a * c = N * 2^(k1+k2+1) := by rw [mul_assoc, hac]
  have e3 : (K * a + N + q * 2^(k1+l1)) * c = 2^(k1+k2+1) * K + N * c + q * 2^(k1+l1) * c := by
    rw [← hac]; ring
  rw [e2, e3] at hmul
  nlinarith

/-- Kernel certificate for one `k`: with `L0 = candL k`, `2^{L0-1} ≤ 3^k` and
`2^{k+1} 3^k + 2^{L0} (2^{⌊k/2⌋+1} + 3^{⌊k/2⌋}) ≤ 2^{L0} 2^{k+1}`. -/
def twoOK (k : ℕ) : Bool :=
  Nat.ble (2^(candL k - 1)) (3^k) &&
    Nat.ble (2^(k+1)*3^k + 2^(candL k)*(2^(k/2+1)+3^(k/2))) (2^(candL k)*2^(k+1))

/-- If `twoOK (k1+k2)` holds, there is no 2-circuit with `k2 ≤ k1` and these block lengths. -/
theorem twoOK_sound {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) (hk : k2 ≤ k1)
    (hok : twoOK (k1+k2) = true) : False := by
  have hsz := two_circuit_size hk h
  have hodd := two_circuit_odd h
  have hL : 0 < k1+l1+k2+l2 := by have := h.1; omega
  have H3 := three_pow_lt_two_pow_of_cycle (by omega) hL h.2.2.2.2.2.2.2.2
  rw [two_circuit_oddSteps h] at H3
  simp only [twoOK, Bool.and_eq_true, Nat.ble_eq] at hok
  obtain ⟨c1, c2⟩ := hok
  generalize k1 + k2 = k at *
  generalize k1 + l1 + k2 + l2 = L at *
  have hc : 1 ≤ candL k := by unfold candL; omega
  generalize candL k = L0 at *
  have hle : L0 ≤ L := by
    by_contra hh
    have : 2 ^ L ≤ 2 ^ (L0 - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  obtain ⟨t, rfl⟩ : ∃ t, L = L0 + t := ⟨L - L0, by omega⟩
  rw [pow_add] at hsz
  have ht : 1 ≤ 2 ^ t := Nat.one_le_two_pow
  set W := 2^(k+1)*3^k
  set A := 2^(k/2+1)+3^(k/2)
  set Q := 2^(k+1)
  have := Nat.mul_le_mul_right (2^t) c2
  have hW : W ≤ W * 2^t := Nat.le_mul_of_pos_right _ ht
  nlinarith

/-- `twoRange lo n` checks `twoOK k` for `lo ≤ k < lo + n`. -/
def twoRange (lo : ℕ) : ℕ → Bool
  | 0 => true
  | n + 1 => twoRange lo n && twoOK (lo + n)

theorem twoRange_sound (lo : ℕ) : ∀ n, twoRange lo n = true → ∀ k, lo ≤ k → k < lo + n →
    twoOK k = true := by
  intro n
  induction n with
  | zero => intro _ k h1 h2; omega
  | succ n ih =>
    intro h k h1 h2
    simp only [twoRange, Bool.and_eq_true] at h
    rcases Nat.lt_or_ge k (lo + n) with hk | hk
    · exact ih h.1 k h1 hk
    · have : k = lo + n := by omega
      subst this; exact h.2

/-- `TwoRange lo hi`: `twoOK k` holds for all `lo ≤ k < hi`. -/
def TwoRange (lo hi : ℕ) : Prop := ∀ k, lo ≤ k → k < hi → twoOK k = true

theorem twoRange_nil (hi : ℕ) : TwoRange hi hi := fun k h1 h2 => absurd h2 (by omega)

theorem twoRange_cons {lo n hi : ℕ} (h : twoRange lo n = true) (hr : TwoRange (lo + n) hi) :
    TwoRange lo hi := fun k h1 h2 => by
  rcases Nat.lt_or_ge k (lo + n) with hk | hk
  · exact twoRange_sound lo n h k h1 hk
  · exact hr k hk h2

theorem twoBlock_0 : twoRange 11 989 = true := by decide +kernel
theorem twoBlock_1 : twoRange 1000 1000 = true := by decide +kernel
theorem twoBlock_2 : twoRange 2000 1000 = true := by decide +kernel
theorem twoBlock_3 : twoRange 3000 1000 = true := by decide +kernel
theorem twoBlock_4 : twoRange 4000 1000 = true := by decide +kernel
theorem twoBlock_5 : twoRange 5000 1000 = true := by decide +kernel
theorem twoBlock_6 : twoRange 6000 1000 = true := by decide +kernel
theorem twoBlock_7 : twoRange 7000 1000 = true := by decide +kernel
theorem twoBlock_8 : twoRange 8000 1000 = true := by decide +kernel
theorem twoBlock_9 : twoRange 9000 1000 = true := by decide +kernel
theorem twoBlock_10 : twoRange 10000 1000 = true := by decide +kernel
theorem twoBlock_11 : twoRange 11000 1000 = true := by decide +kernel
theorem twoBlock_12 : twoRange 12000 1000 = true := by decide +kernel
theorem twoBlock_13 : twoRange 13000 1000 = true := by decide +kernel
theorem twoBlock_14 : twoRange 14000 1000 = true := by decide +kernel
theorem twoBlock_15 : twoRange 15000 1000 = true := by decide +kernel
theorem twoBlock_16 : twoRange 16000 1000 = true := by decide +kernel
theorem twoBlock_17 : twoRange 17000 1000 = true := by decide +kernel
theorem twoBlock_18 : twoRange 18000 1000 = true := by decide +kernel
theorem twoBlock_19 : twoRange 19000 1000 = true := by decide +kernel
theorem twoBlock_20 : twoRange 20000 1000 = true := by decide +kernel
theorem twoBlock_21 : twoRange 21000 1000 = true := by decide +kernel
theorem twoBlock_22 : twoRange 22000 1000 = true := by decide +kernel
theorem twoBlock_23 : twoRange 23000 1000 = true := by decide +kernel
theorem twoBlock_24 : twoRange 24000 1000 = true := by decide +kernel
theorem twoBlock_25 : twoRange 25000 1000 = true := by decide +kernel
theorem twoBlock_26 : twoRange 26000 1000 = true := by decide +kernel
theorem twoBlock_27 : twoRange 27000 1000 = true := by decide +kernel
theorem twoBlock_28 : twoRange 28000 1000 = true := by decide +kernel
theorem twoBlock_29 : twoRange 29000 1000 = true := by decide +kernel
theorem twoBlock_30 : twoRange 30000 1000 = true := by decide +kernel
theorem twoBlock_31 : twoRange 31000 1000 = true := by decide +kernel
theorem twoBlock_32 : twoRange 32000 1000 = true := by decide +kernel
theorem twoBlock_33 : twoRange 33000 1000 = true := by decide +kernel
theorem twoBlock_34 : twoRange 34000 1000 = true := by decide +kernel
theorem twoBlock_35 : twoRange 35000 1000 = true := by decide +kernel
theorem twoBlock_36 : twoRange 36000 1000 = true := by decide +kernel
theorem twoBlock_37 : twoRange 37000 1000 = true := by decide +kernel
theorem twoBlock_38 : twoRange 38000 1000 = true := by decide +kernel
theorem twoBlock_39 : twoRange 39000 1000 = true := by decide +kernel
theorem twoBlock_40 : twoRange 40000 1000 = true := by decide +kernel
theorem twoBlock_41 : twoRange 41000 1000 = true := by decide +kernel
theorem twoBlock_42 : twoRange 42000 1000 = true := by decide +kernel
theorem twoBlock_43 : twoRange 43000 1000 = true := by decide +kernel
theorem twoBlock_44 : twoRange 44000 1000 = true := by decide +kernel
theorem twoBlock_45 : twoRange 45000 1000 = true := by decide +kernel
theorem twoBlock_46 : twoRange 46000 1000 = true := by decide +kernel
theorem twoBlock_47 : twoRange 47000 1000 = true := by decide +kernel
theorem twoBlock_48 : twoRange 48000 1000 = true := by decide +kernel
theorem twoBlock_49 : twoRange 49000 1000 = true := by decide +kernel
theorem twoBlock_50 : twoRange 50000 1000 = true := by decide +kernel
theorem twoBlock_51 : twoRange 51000 1000 = true := by decide +kernel
theorem twoBlock_52 : twoRange 52000 1000 = true := by decide +kernel
theorem twoBlock_53 : twoRange 53000 1000 = true := by decide +kernel
theorem twoBlock_54 : twoRange 54000 1000 = true := by decide +kernel
theorem twoBlock_55 : twoRange 55000 1000 = true := by decide +kernel
theorem twoBlock_56 : twoRange 56000 1000 = true := by decide +kernel
theorem twoBlock_57 : twoRange 57000 1000 = true := by decide +kernel
theorem twoBlock_58 : twoRange 58000 1000 = true := by decide +kernel
theorem twoBlock_59 : twoRange 59000 1000 = true := by decide +kernel
theorem twoBlock_60 : twoRange 60000 1000 = true := by decide +kernel
theorem twoBlock_61 : twoRange 61000 1000 = true := by decide +kernel
theorem twoBlock_62 : twoRange 62000 1000 = true := by decide +kernel
theorem twoBlock_63 : twoRange 63000 1000 = true := by decide +kernel
theorem twoBlock_64 : twoRange 64000 1000 = true := by decide +kernel
theorem twoBlock_65 : twoRange 65000 1000 = true := by decide +kernel
theorem twoBlock_66 : twoRange 66000 1000 = true := by decide +kernel
theorem twoBlock_67 : twoRange 67000 1000 = true := by decide +kernel
theorem twoBlock_68 : twoRange 68000 1000 = true := by decide +kernel
theorem twoBlock_69 : twoRange 69000 1000 = true := by decide +kernel
theorem twoBlock_70 : twoRange 70000 1000 = true := by decide +kernel
theorem twoBlock_71 : twoRange 71000 1000 = true := by decide +kernel
theorem twoBlock_72 : twoRange 72000 1000 = true := by decide +kernel
theorem twoBlock_73 : twoRange 73000 1000 = true := by decide +kernel
theorem twoBlock_74 : twoRange 74000 1000 = true := by decide +kernel
theorem twoBlock_75 : twoRange 75000 1000 = true := by decide +kernel
theorem twoBlock_76 : twoRange 76000 1000 = true := by decide +kernel
theorem twoBlock_77 : twoRange 77000 1000 = true := by decide +kernel
theorem twoBlock_78 : twoRange 78000 1000 = true := by decide +kernel
theorem twoBlock_79 : twoRange 79000 1000 = true := by decide +kernel
theorem twoBlock_80 : twoRange 80000 1000 = true := by decide +kernel
theorem twoBlock_81 : twoRange 81000 1000 = true := by decide +kernel
theorem twoBlock_82 : twoRange 82000 1000 = true := by decide +kernel
theorem twoBlock_83 : twoRange 83000 1000 = true := by decide +kernel
theorem twoBlock_84 : twoRange 84000 1000 = true := by decide +kernel
theorem twoBlock_85 : twoRange 85000 1000 = true := by decide +kernel
theorem twoBlock_86 : twoRange 86000 1000 = true := by decide +kernel
theorem twoBlock_87 : twoRange 87000 1000 = true := by decide +kernel
theorem twoBlock_88 : twoRange 88000 1000 = true := by decide +kernel
theorem twoBlock_89 : twoRange 89000 1000 = true := by decide +kernel
theorem twoBlock_90 : twoRange 90000 1000 = true := by decide +kernel
theorem twoBlock_91 : twoRange 91000 1000 = true := by decide +kernel
theorem twoBlock_92 : twoRange 92000 1000 = true := by decide +kernel
theorem twoBlock_93 : twoRange 93000 1000 = true := by decide +kernel
theorem twoBlock_94 : twoRange 94000 1000 = true := by decide +kernel
theorem twoBlock_95 : twoRange 95000 1000 = true := by decide +kernel
theorem twoBlock_96 : twoRange 96000 1000 = true := by decide +kernel
theorem twoBlock_97 : twoRange 97000 1000 = true := by decide +kernel
theorem twoBlock_98 : twoRange 98000 1000 = true := by decide +kernel
theorem twoBlock_99 : twoRange 99000 1000 = true := by decide +kernel

/-- Kernel-verified: `twoOK k` for all `11 ≤ k < 100000`. -/
theorem twoRange_11_100000 : TwoRange 11 100000 :=
  twoRange_cons twoBlock_0 (twoRange_cons twoBlock_1 (twoRange_cons twoBlock_2 (twoRange_cons twoBlock_3 (twoRange_cons twoBlock_4 (twoRange_cons twoBlock_5 (twoRange_cons twoBlock_6 (twoRange_cons twoBlock_7 (twoRange_cons twoBlock_8 (twoRange_cons twoBlock_9 (twoRange_cons twoBlock_10 (twoRange_cons twoBlock_11 (twoRange_cons twoBlock_12 (twoRange_cons twoBlock_13 (twoRange_cons twoBlock_14 (twoRange_cons twoBlock_15 (twoRange_cons twoBlock_16 (twoRange_cons twoBlock_17 (twoRange_cons twoBlock_18 (twoRange_cons twoBlock_19 (twoRange_cons twoBlock_20 (twoRange_cons twoBlock_21 (twoRange_cons twoBlock_22 (twoRange_cons twoBlock_23 (twoRange_cons twoBlock_24 (twoRange_cons twoBlock_25 (twoRange_cons twoBlock_26 (twoRange_cons twoBlock_27 (twoRange_cons twoBlock_28 (twoRange_cons twoBlock_29 (twoRange_cons twoBlock_30 (twoRange_cons twoBlock_31 (twoRange_cons twoBlock_32 (twoRange_cons twoBlock_33 (twoRange_cons twoBlock_34 (twoRange_cons twoBlock_35 (twoRange_cons twoBlock_36 (twoRange_cons twoBlock_37 (twoRange_cons twoBlock_38 (twoRange_cons twoBlock_39 (twoRange_cons twoBlock_40 (twoRange_cons twoBlock_41 (twoRange_cons twoBlock_42 (twoRange_cons twoBlock_43 (twoRange_cons twoBlock_44 (twoRange_cons twoBlock_45 (twoRange_cons twoBlock_46 (twoRange_cons twoBlock_47 (twoRange_cons twoBlock_48 (twoRange_cons twoBlock_49 (twoRange_cons twoBlock_50 (twoRange_cons twoBlock_51 (twoRange_cons twoBlock_52 (twoRange_cons twoBlock_53 (twoRange_cons twoBlock_54 (twoRange_cons twoBlock_55 (twoRange_cons twoBlock_56 (twoRange_cons twoBlock_57 (twoRange_cons twoBlock_58 (twoRange_cons twoBlock_59 (twoRange_cons twoBlock_60 (twoRange_cons twoBlock_61 (twoRange_cons twoBlock_62 (twoRange_cons twoBlock_63 (twoRange_cons twoBlock_64 (twoRange_cons twoBlock_65 (twoRange_cons twoBlock_66 (twoRange_cons twoBlock_67 (twoRange_cons twoBlock_68 (twoRange_cons twoBlock_69 (twoRange_cons twoBlock_70 (twoRange_cons twoBlock_71 (twoRange_cons twoBlock_72 (twoRange_cons twoBlock_73 (twoRange_cons twoBlock_74 (twoRange_cons twoBlock_75 (twoRange_cons twoBlock_76 (twoRange_cons twoBlock_77 (twoRange_cons twoBlock_78 (twoRange_cons twoBlock_79 (twoRange_cons twoBlock_80 (twoRange_cons twoBlock_81 (twoRange_cons twoBlock_82 (twoRange_cons twoBlock_83 (twoRange_cons twoBlock_84 (twoRange_cons twoBlock_85 (twoRange_cons twoBlock_86 (twoRange_cons twoBlock_87 (twoRange_cons twoBlock_88 (twoRange_cons twoBlock_89 (twoRange_cons twoBlock_90 (twoRange_cons twoBlock_91 (twoRange_cons twoBlock_92 (twoRange_cons twoBlock_93 (twoRange_cons twoBlock_94 (twoRange_cons twoBlock_95 (twoRange_cons twoBlock_96 (twoRange_cons twoBlock_97 (twoRange_cons twoBlock_98 (twoRange_cons twoBlock_99 (twoRange_nil 100000))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))

/-- The certificate genuinely discriminates: it fails at `k = 10`. -/
example : twoOK 10 = false := by decide

/-- Non-vacuity: the doubled trivial cycle `1 → 2 → 1 → 2 → 1` is a 2-circuit. -/
example : IsTwoCircuit 1 1 1 1 1 := by
  refine ⟨le_rfl, le_rfl, le_rfl, le_rfl, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Main result.** Every 2-circuit with `k1 + k2 < 100000` odd steps is trivial: `m = 1`. -/
theorem two_circuit_eq_one {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2)
    (hk : k1 + k2 < 100000) : m = 1 := by
  by_contra hm1
  have hodd := two_circuit_odd h
  have hL : 0 < k1+l1+k2+l2 := by have := h.1; omega
  have hb := oddSteps_ge_of_cycle (by omega) hL h.2.2.2.2.2.2.2.2 hm1 (by omega)
  rw [two_circuit_oddSteps h] at hb
  rcases le_or_gt k2 k1 with hk21 | hk12
  · exact twoOK_sound h hk21 (twoRange_11_100000 _ (by omega) hk)
  · have h' := two_circuit_rotate h
    exact twoOK_sound h' hk12.le (by rw [add_comm]; exact twoRange_11_100000 _ (by omega) hk)

/-- Contrapositive: a 2-circuit with `m > 1` has at least `100000` odd steps. -/
theorem two_circuit_k_ge {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) (hm : 1 < m) :
    100000 ≤ k1 + k2 := by
  by_contra hc
  have := two_circuit_eq_one h (by omega)
  omega

/-- `2^158496 ≤ 3^100000` (kernel, GMP-accelerated). -/
theorem two_pow_158496_le : 2 ^ 158496 ≤ 3 ^ 100000 := by decide +kernel

theorem L_ge_of_k_ge_aux {k L a b : ℕ} (hab : 2 ^ b ≤ 3 ^ a) (hk : a ≤ k)
    (h : 3 ^ k < 2 ^ L) : b + 1 ≤ L := by
  by_contra hc
  have h1 : 3 ^ a ≤ 3 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  have h2 : 2 ^ L ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
  omega

/-- `k ≥ 100000` and `3^k < 2^L` imply `L ≥ 158497`. -/
theorem L_ge_of_k_ge {k L : ℕ} (hk : 100000 ≤ k) (h : 3 ^ k < 2 ^ L) : 158497 ≤ L :=
  L_ge_of_k_ge_aux two_pow_158496_le hk h

/-- A nontrivial 1-circuit has length `k + l ≥ 158497`. -/
theorem one_circuit_L_ge {m k l : ℕ} (h : IsOneCircuit m k l) (hm : 1 < m) : 158497 ≤ k + l :=
  L_ge_of_k_ge (one_circuit_k_ge h hm) (one_circuit_size h).2.1

/-- A nontrivial 2-circuit has length `k1 + l1 + k2 + l2 ≥ 158497`. -/
theorem two_circuit_L_ge {m k1 l1 k2 l2 : ℕ} (h : IsTwoCircuit m k1 l1 k2 l2) (hm : 1 < m) :
    158497 ≤ k1 + l1 + k2 + l2 := by
  have hodd := two_circuit_odd h
  have hL : 0 < k1+l1+k2+l2 := by have := h.1; omega
  have H3 := three_pow_lt_two_pow_of_cycle (by omega) hL h.2.2.2.2.2.2.2.2
  rw [two_circuit_oddSteps h] at H3
  exact L_ge_of_k_ge (two_circuit_k_ge h hm) H3

end Collatz

#print axioms Collatz.two_circuit_oddSteps
#print axioms Collatz.two_circuit_eq
#print axioms Collatz.two_circuit_dvd
#print axioms Collatz.two_circuit_rotate
#print axioms Collatz.two_circuit_size
#print axioms Collatz.twoOK_sound
#print axioms Collatz.twoBlock_0
#print axioms Collatz.twoRange_11_100000
#print axioms Collatz.two_circuit_eq_one
#print axioms Collatz.two_circuit_k_ge
#print axioms Collatz.two_pow_158496_le
#print axioms Collatz.one_circuit_L_ge
#print axioms Collatz.two_circuit_L_ge
