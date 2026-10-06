import RunsTail
import RunsBridge
import Collatz.CycleBasic
import Sieve24
import Merge

/-!
# C-level run bounds (`CRuns`)

**Status: Unconditional, CLASSICAL** (Steiner 1977 / Simons 2005 / Simons–de Weger 2005, via
the in-house `PadeSup`/`FewRunsUncond`/`RunsTail` proofs `few_runs_cycle_trivial_uncond`, `runs_ge_18_uncond`), restated
for the classical map `C`.

Intrinsic invariant: along a cycle, the number of odd runs equals the number of cycle elements
`≡ 1 (mod 4)` (an odd `x` has `T x` even iff `x ≡ 1 mod 4`; even→odd and odd→even transitions
are equinumerous on a cycle; the intermediate `C`-values `3x+1` are even, hence never `≡ 1`).

* `orbCount f P j n` generic orbit filter count; `orbCount_succ`, `orbCount_add` (cocycle),
  `orbCount_shift` (cyclic shift invariance on an `f`-cycle).
* `t4`, `c4`, `codd`: counts of `T`-iterates `≡1 (4)`, `C`-iterates `≡1 (4)`, odd `C`-iterates.
* `T_even_iff_mod4`, `oddRuns_eq_t4` (on a `T`-cycle, `oddRuns L x = t4 L x`), `count_shift_C`.
* `lift_joint` / `iterate_C_add_oddSteps` / `c4_add_oddSteps` / `codd_add_oddSteps`:
  `C^{j+S_j(n)} n = T^j n` with matching counts; `exists_iterate_T_of_C_exact`.
* `C_cycle_runs_ge_18`, `C_cycle_few_runs_trivial`: main C-level statements.
* `cycle_runstart_merge_ge`: naming alias of `Merge.cycle_localmin_ge` (`Merge` repair).
-/

namespace Collatz
open CollatzProof

/-- generic filter count along the orbit of `f`. -/
def orbCount (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] (j n : ℕ) : ℕ :=
  ((Finset.range j).filter (fun i => P (f^[i] n))).card

theorem orbCount_eq_sum (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] (j n : ℕ) :
    orbCount f P j n = ∑ i ∈ Finset.range j, if P (f^[i] n) then 1 else 0 := by
  unfold orbCount; rw [Finset.card_filter]

theorem orbCount_succ (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] (j n : ℕ) :
    orbCount f P (j+1) n = (if P n then 1 else 0) + orbCount f P j (f n) := by
  rw [orbCount_eq_sum, orbCount_eq_sum, Finset.sum_range_succ', add_comm]
  simp only [Function.iterate_succ_apply, Function.iterate_zero, id]
  rfl

theorem orbCount_zero (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] (n : ℕ) :
    orbCount f P 0 n = 0 := by simp [orbCount]

/-- cocycle -/
theorem orbCount_add (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] (a b n : ℕ) :
    orbCount f P (a+b) n = orbCount f P a n + orbCount f P b (f^[a] n) := by
  induction a generalizing n with
  | zero => simp [orbCount_zero]
  | succ a ih =>
    rw [show a + 1 + b = (a+b) + 1 by omega, orbCount_succ, orbCount_succ, ih,
      Function.iterate_succ_apply]; omega

/-- shift invariance on a cycle -/
theorem orbCount_shift_one (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] {ℓ m : ℕ}
    (hc : f^[ℓ] m = m) : orbCount f P ℓ (f m) = orbCount f P ℓ m := by
  have h1 := orbCount_add f P ℓ 1 m
  have h2 := orbCount_add f P 1 ℓ m
  rw [add_comm] at h2
  rw [h1, hc] at h2
  simp only [Function.iterate_one] at h2
  omega

theorem orbCount_shift (f : ℕ → ℕ) (P : ℕ → Prop) [DecidablePred P] {ℓ m : ℕ}
    (hc : f^[ℓ] m = m) (t : ℕ) : orbCount f P ℓ (f^[t] m) = orbCount f P ℓ m := by
  induction t generalizing m with
  | zero => rfl
  | succ t ih =>
    have hc' : f^[ℓ] (f m) = f m := by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hc]
    rw [Function.iterate_succ_apply, ih hc', orbCount_shift_one f P hc]

def t4 (j n : ℕ) : ℕ := ((Finset.range j).filter (fun i => T^[i] n % 4 = 1)).card
def c4 (j n : ℕ) : ℕ := ((Finset.range j).filter (fun i => C^[i] n % 4 = 1)).card
def codd (j n : ℕ) : ℕ := ((Finset.range j).filter (fun i => C^[i] n % 2 = 1)).card

theorem t4_eq (j n : ℕ) : t4 j n = orbCount T (fun x => x % 4 = 1) j n := rfl
theorem c4_eq (j n : ℕ) : c4 j n = orbCount C (fun x => x % 4 = 1) j n := rfl
theorem codd_eq (j n : ℕ) : codd j n = orbCount C (fun x => x % 2 = 1) j n := rfl

theorem T_even_iff_mod4 {x : ℕ} (hx : x % 2 = 1) : T x % 2 = 0 ↔ x % 4 = 1 := by
  rw [T_of_odd hx]; omega

theorem oddRuns_eq_t4 {L x : ℕ} (hc : T^[L] x = x) : oddRuns L x = t4 L x := by
  let p : ℕ → ℕ := fun i => T^[i] x % 2
  let f : ℕ → ℕ := fun i => if T^[i] x % 4 = 1 then 1 else 0
  have hpt : ∀ i, p (i+1) + f i = p i + runStart (T^[i] x) := by
    intro i
    simp only [p, f, runStart]
    rw [Function.iterate_succ_apply']
    rcases Nat.mod_two_eq_zero_or_one (T^[i] x) with h | h
    · have : ¬ T^[i] x % 4 = 1 := by omega
      simp only [this, ite_false, h, true_and]
      rcases Nat.mod_two_eq_zero_or_one (T (T^[i] x)) with h' | h' <;> simp [h']
    · have key := T_even_iff_mod4 h
      simp only [h, show ¬ (1 = 0) from by omega, false_and, ite_false]
      by_cases h4 : T^[i] x % 4 = 1
      · simp only [h4, ite_true]; have := key.2 h4; omega
      · simp only [h4, ite_false]
        rcases Nat.mod_two_eq_zero_or_one (T (T^[i] x)) with h' | h'
        · exact absurd (key.1 h') h4
        · omega
  have hsum := Finset.sum_congr rfl (fun i (_ : i ∈ Finset.range L) => hpt i)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at hsum
  have hshift : ∑ i ∈ Finset.range L, p (i+1) = ∑ i ∈ Finset.range L, p i := by
    have a := Finset.sum_range_succ' p L
    have b := Finset.sum_range_succ p L
    have : p L = p 0 := by simp only [p, hc, Function.iterate_zero, id]
    omega
  rw [oddRuns_eq_sum, t4_eq, orbCount_eq_sum]
  change _ = ∑ i ∈ Finset.range L, f i
  omega

theorem count_shift_C {ℓ m : ℕ} (hc : C^[ℓ] m = m) (P : ℕ → Prop) [DecidablePred P] (t : ℕ) :
    ((Finset.range ℓ).filter (fun i => P (C^[i] (C^[t] m)))).card =
      ((Finset.range ℓ).filter (fun i => P (C^[i] m))).card :=
  orbCount_shift C P hc t

/-- Joint lifting: C-length `j + oddSteps j n` realises `T^[j]` and the counts. -/
theorem lift_joint (j n : ℕ) :
    C^[j + oddSteps j n] n = T^[j] n ∧ c4 (j + oddSteps j n) n = t4 j n ∧
      codd (j + oddSteps j n) n = oddSteps j n := by
  induction j generalizing n with
  | zero => simp [oddSteps, c4, codd, t4]
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih (T n)
    simp only [c4_eq, codd_eq, t4_eq] at h2 h3 ⊢
    rcases Nat.mod_two_eq_zero_or_one n with hn | hn
    · have e : j + 1 + oddSteps (j+1) n = (j + oddSteps j (T n)) + 1 := by
        simp only [oddSteps, hn]; omega
      have n4 : ¬ n % 4 = 1 := by omega
      have n2 : ¬ n % 2 = 1 := by omega
      rw [e, orbCount_succ, orbCount_succ, orbCount_succ, ← T_eq_C_of_even hn,
        Function.iterate_succ_apply, Function.iterate_succ_apply, ← T_eq_C_of_even hn, h1]
      simp only [n4, n2, ite_false, zero_add]
      refine ⟨trivial, h2, ?_⟩
      rw [h3]; simp [oddSteps, hn]
    · have e : j + 1 + oddSteps (j+1) n = (j + oddSteps j (T n)) + 1 + 1 := by
        simp only [oddSteps, hn]; omega
      have c2 : ¬ (C n) % 2 = 1 := by rw [C_of_odd hn]; omega
      have c4' : ¬ (C n) % 4 = 1 := by rw [C_of_odd hn]; omega
      rw [e, orbCount_succ, orbCount_succ, orbCount_succ, orbCount_succ, orbCount_succ,
        ← T_eq_C_C_of_odd hn, Function.iterate_succ_apply, Function.iterate_succ_apply,
        ← T_eq_C_C_of_odd hn, Function.iterate_succ_apply, h1, h2, h3]
      simp only [c2, c4', ite_false, zero_add, hn, ite_true]
      refine ⟨trivial, trivial, ?_⟩
      simp [oddSteps, hn]; omega

theorem iterate_C_add_oddSteps (j n : ℕ) : C^[j + oddSteps j n] n = T^[j] n := (lift_joint j n).1
theorem c4_add_oddSteps (j n : ℕ) : c4 (j + oddSteps j n) n = t4 j n := (lift_joint j n).2.1
theorem codd_add_oddSteps (j n : ℕ) : codd (j + oddSteps j n) n = oddSteps j n :=
  (lift_joint j n).2.2

/-- **Exact lifting.** If `i = 0` or `C^{i-1} x` is even, then `C^i x = T^j x` with
`j + oddSteps j x = i` exactly. -/
theorem exists_iterate_T_of_C_exact (i x : ℕ) (hi : ∀ i', i = i' + 1 → C^[i'] x % 2 = 0) :
    ∃ j, j + oddSteps j x = i ∧ T^[j] x = C^[i] x := by
  induction i using Nat.strong_induction_on generalizing x with
  | _ i ih =>
    match i, ih, hi with
    | 0, _, _ => exact ⟨0, by simp [oddSteps], rfl⟩
    | i' + 1, ih, hi =>
      rcases Nat.mod_two_eq_zero_or_one x with hx | hx
      · obtain ⟨j', hj', hT⟩ := ih i' (by omega) (C x) (by
          intro i'' hi''
          have := hi i' rfl
          rw [hi'', Function.iterate_succ_apply] at this
          exact this)
        refine ⟨j' + 1, ?_, ?_⟩
        · simp only [oddSteps, hx, T_eq_C_of_even hx]; omega
        · rw [Function.iterate_succ_apply, T_eq_C_of_even hx, hT, ← Function.iterate_succ_apply]
      · match i', ih, hi with
        | 0, _, hi =>
          have := hi 0 rfl
          simp at this; omega
        | i'' + 1, ih, hi =>
          obtain ⟨j'', hj'', hT⟩ := ih i'' (by omega) (C (C x)) (by
            intro k hk
            have := hi (i'' + 1) rfl
            rw [hk, show k + 1 + 1 = k + 2 by ring, Function.iterate_add_apply] at this
            exact this)
          refine ⟨j'' + 1, ?_, ?_⟩
          · simp only [oddSteps, hx, T_eq_C_C_of_odd hx]; omega
          · rw [Function.iterate_succ_apply, T_eq_C_C_of_odd hx, hT, ← iterate_C_two,
              ← Function.iterate_add_apply]

/-- Variant of `exists_min_odd_T_cycle_aux` that also exports `C^[ℓ] m = m`. -/
theorem exists_min_odd_T_cycle_aux' (n : ℕ) (hn : 0 < n) (ℓ : ℕ) (hℓ : 0 < ℓ)
    (h : C^[ℓ] n = n) :
    ∃ m, 0 < m ∧ m % 2 = 1 ∧ C^[ℓ] m = m ∧ (∀ j, m ≤ T^[j] m) ∧ m ≤ n ∧
      ∃ t, C^[t] m = n := by
  have hne : (Finset.range ℓ).Nonempty := ⟨0, by simpa using hℓ⟩
  obtain ⟨j0, hj0, hmin⟩ := Finset.exists_min_image (Finset.range ℓ) (fun j => C^[j] n) hne
  rw [Finset.mem_range] at hj0
  set m := C^[j0] n with hm
  have hper : Function.IsPeriodicPt C ℓ n := h
  have h1 : ∀ t, m ≤ C^[t] n := by
    intro t
    rw [← hper.iterate_mod_apply]
    exact hmin _ (Finset.mem_range.2 (Nat.mod_lt _ hℓ))
  have h2 : ∀ t, m ≤ C^[t] m := by
    intro t; rw [hm, ← Function.iterate_add_apply]; exact h1 _
  have hmℓ : C^[ℓ] m = m := by
    rw [hm, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, h]
  have hmpos : 0 < m := iterate_C_pos hn j0
  have hmodd : m % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one m with he | ho
    · have := h2 1
      rw [Function.iterate_one, C_of_even he] at this
      omega
    · exact ho
  have hback : C^[ℓ - j0] m = n := by
    rw [hm, ← Function.iterate_add_apply, Nat.sub_add_cancel hj0.le, h]
  have hmn : m ≤ n := by simpa using h1 0
  refine ⟨m, hmpos, hmodd, hmℓ, ?_, hmn, _, hback⟩
  intro j
  obtain ⟨i, hi⟩ := exists_iterate_T_eq_iterate_C j m
  rw [hi]; exact h2 i

/-- **C-level run theorem (classical, restated for `C`).** A nontrivial positive `C`-cycle
`C^ℓ n = n` has at least 18 iterates `≡ 1 (mod 4)` among `n, C n, …, C^{ℓ-1} n`
(this count equals the number of odd runs in the window); at least 29 unless it has fewer
than 225644606 odd iterates in the window; at least 42 if it has at least `10^11` odd
iterates.

Proof bookkeeping: the identification `c4 ℓ n = oddRuns L m` is made at the odd orbit minimum
`m` of the cycle, with `L` the matching `T`-length (`L + S_L(m) = ℓ`, i.e. the window of `ℓ`
`C`-steps starting at `m` is exactly `L` `T`-steps).  `ℓ` need not be the minimal period: if
`ℓ = t · (minimal period)`, both counts `c4 ℓ n` and `codd ℓ n` are `t` times their values at the
minimal period, so the bounds are weakest (and still valid) at the minimal period. -/
theorem C_cycle_runs_ge_18 {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hne : ¬ (n = 1 ∨ n = 2 ∨ n = 4)) :
    18 ≤ c4 ℓ n ∧ (29 ≤ c4 ℓ n ∨ codd ℓ n < 225644606) ∧ (10^11 ≤ codd ℓ n → 42 ≤ c4 ℓ n) := by
  obtain ⟨m, hmpos, hodd, hmℓ, hmin, -, t, ht⟩ := exists_min_odd_T_cycle_aux' n hn ℓ hℓ h
  obtain ⟨L, hLℓ, hTL⟩ := exists_iterate_T_of_C_exact ℓ m (by
    intro i hi
    rcases Nat.mod_two_eq_zero_or_one (C^[i] m) with he | ho
    · exact he
    · exfalso
      have := hmℓ
      rw [hi, Function.iterate_succ_apply', C_of_odd ho] at this
      omega)
  have hc : T^[L] m = m := hTL.trans hmℓ
  have hL : 0 < L := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp [oddSteps] at hLℓ; omega
    · exact h0
  have ec4 : c4 ℓ n = oddRuns L m := by
    rw [← ht, c4_eq, orbCount_shift C _ hmℓ t, ← c4_eq, ← hLℓ, c4_add_oddSteps,
      oddRuns_eq_t4 hc]
  have ecodd : codd ℓ n = oddSteps L m := by
    rw [← ht, codd_eq, orbCount_shift C _ hmℓ t, ← codd_eq, ← hLℓ, codd_add_oddSteps]
  have h1 : 1 < m := by
    by_contra h1
    obtain rfl : m = 1 := by omega
    exact hne (ht ▸ iterate_C_one_mem t)
  have h24 := min_orbit_ge_24 h1 hmin
  rw [ec4, ecodd]
  exact runs_ge_18_uncond hodd h24 hmin hL hc

/-- **Corollary (C-form of the `PadeSup`/`FewRunsUncond`/`RunsTail` run bounds).** A positive `C`-cycle with at most 17
iterates `≡ 1 (mod 4)` per window of length `ℓ` is the trivial cycle. -/
theorem C_cycle_few_runs_trivial {n ℓ : ℕ} (hn : 0 < n) (hℓ : 0 < ℓ) (h : C^[ℓ] n = n)
    (hr : c4 ℓ n ≤ 17) : n = 1 ∨ n = 2 ∨ n = 4 := by
  by_contra hne
  have := (C_cycle_runs_ge_18 hn hℓ h hne).1
  omega

example : c4 3 1 = 1 := by decide
example : codd 3 1 = 1 := by decide
example : C^[3] 1 = 1 := by decide
example : t4 2 1 = 1 ∧ oddRuns 2 1 = 1 := by decide

/-- **Alias of `cycle_localmin_ge`** (`Merge` naming repair). `x` is NOT assumed to be a local
minimum: only a point of a `T`-cycle that is an odd run start (`x+1 = 2^k b`, `k ≥ 1`, `b` odd)
whose run is followed by at least 2 even steps (`3^k b ≡ 1 mod 4`). Conclusion `2X0+1 ≤ x`.
It does not raise the cycle-minimum floor (still `min_orbit_ge_24`). -/
theorem cycle_runstart_merge_ge {X0 x L k b : ℕ}
    (HX : ∀ m, 1 < m → (∀ j, m ≤ T^[j] m) → X0 ≤ m)
    (hL : 0 < L) (hc : T^[L] x = x) (hk : 1 ≤ k) (hb : b % 2 = 1)
    (hn : x + 1 = 2^k * b) (h4 : (3^k * b) % 4 = 1) : 2 * X0 + 1 ≤ x :=
  cycle_localmin_ge HX hL hc hk hb hn h4

end Collatz

#print axioms Collatz.C_cycle_runs_ge_18
#print axioms Collatz.C_cycle_few_runs_trivial
#print axioms Collatz.oddRuns_eq_t4
#print axioms Collatz.exists_iterate_T_of_C_exact
#print axioms Collatz.lift_joint
#print axioms Collatz.count_shift_C
#print axioms Collatz.T_even_iff_mod4
#print axioms Collatz.exists_min_odd_T_cycle_aux'
#print axioms Collatz.cycle_runstart_merge_ge
