import NormAll
import CollatzSearch.ChristoffelMin

/-!
# bridge from the one-move theorems to actual `T`-cycles (DIRECTIVES 2(a))

* `cycle_word_eq`: if the odd steps of the `T`-orbit of `m` in its first `L` steps are exactly at
  the partial sums `psum v i` (`i < r`, all `v i ≥ 1`, `psum v r = L`) and `T^L m = m`, then
  `(2^L - 3^r) m = B(v)` (Böhm–Sontacchi cycle equation, via `ChristoffelMin.bsum_affine`).
* `cycle_one_move_christoffel`: such a cycle with `r ≥ 2` whose word is `chr r L` or one move
  from it is the trivial cycle (`L = 2r`, `v = (2,…,2)`, `m = 1`). Uses `NormAll` (all `(r, L)`).

Prior art to credit: Knight (Christoffel words), Lebel, Mghirbi (E = 1), Solomon (left-flip
one-swaps and the non-coprime factor). The one-move statement for all moves incl. wraps and all
`(r, L)` is (as far as we know) new; see experiments/NORM_CRITERION.md.
-/

namespace CollatzSearch.NormBridge
open CollatzSearch.NormGoal CollatzSearch.NormAll CollatzProof Finset

/-- Partial sums are monotone. -/
theorem psum_mono (v : ℕ → ℕ) {a b : ℕ} (h : a ≤ b) : psum v a ≤ psum v b :=
  sum_le_sum_of_subset (range_subset_range.mpr h)

/-- `psum v (i+1) = psum v i + v i`. -/
theorem psum_succ (v : ℕ → ℕ) (i : ℕ) : psum v (i + 1) = psum v i + v i := by
  simp [psum, sum_range_succ]

/-- Horner step: `B_{i+1}(v) = 3 B_i(v) + 2^{psum v i}`. -/
theorem Bnum_succ (v : ℕ → ℕ) (i : ℕ) : Bnum (i + 1) v = 3 * Bnum i v + 2 ^ psum v i := by
  unfold Bnum
  rw [sum_range_succ, mul_sum]
  simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, one_mul]
  congr 1
  apply sum_congr rfl
  intro j hj
  have := mem_range.mp hj
  rw [show i - j = (i - 1 - j) + 1 by omega, pow_succ]; ring

/-- **Cycle word equation (T-map).** If the odd steps of the `T`-orbit of `m` during `L` steps
sit exactly at the partial sums `psum v i`, `i < r` (entries `v i ≥ 1`, `psum v r = L`), and
`T^L m = m`, then `(2^L - 3^r) · m = B(v)`. -/
theorem cycle_word_eq {m L r : ℕ} {v : ℕ → ℕ} (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m) :
    (2 ^ L - 3 ^ r) * m = Bnum r v := by
  have claim : ∀ i ≤ r, oddSteps (psum v i) m = i ∧ bsum (psum v i) m = Bnum i v := by
    intro i
    induction i with
    | zero => intro _; simp [psum, oddSteps, bsum, Bnum]
    | succ i ih =>
      intro hi
      obtain ⟨ih1, ih2⟩ := ih (by omega)
      have hvi := hv1 i (by omega)
      have hLi : psum v (i + 1) ≤ L := hL ▸ psum_mono v hi
      rw [psum_succ] at hLi
      have inner : ∀ s, 1 ≤ s → s ≤ v i →
          oddSteps (psum v i + s) m = i + 1 ∧ bsum (psum v i + s) m = Bnum (i + 1) v := by
        intro s hs1 hs2
        induction s with
        | zero => omega
        | succ s ihs =>
          rcases Nat.eq_zero_or_pos s with h0 | hpos
          · subst h0
            have hodd1 : T^[psum v i] m % 2 = 1 :=
              (hodd (psum v i) (by omega)).mpr ⟨i, by omega, rfl⟩
            rw [← add_assoc, add_zero, oddSteps_succ_last, Bnum_succ]
            simp only [bsum, hodd1, ite_true]
            rw [ih1, ih2]; exact ⟨rfl, rfl⟩
          · obtain ⟨e1, e2⟩ := ihs hpos (by omega)
            have heven : T^[psum v i + s] m % 2 = 0 := by
              have : ¬ T^[psum v i + s] m % 2 = 1 := by
                rw [hodd _ (by omega)]
                rintro ⟨i', hi', heq⟩
                rcases Nat.lt_or_ge i i' with h | h
                · have := psum_mono v (show i + 1 ≤ i' by omega)
                  rw [psum_succ] at this; omega
                · have := psum_mono v h; omega
              omega
            rw [← add_assoc, oddSteps_succ_last, heven, add_zero]
            simp only [bsum, heven, zero_ne_one, ite_false]
            exact ⟨e1, e2⟩
      rw [psum_succ]
      exact inner (v i) hvi le_rfl
  obtain ⟨c1, c2⟩ := claim r le_rfl
  rw [hL] at c1 c2
  have haff := bsum_affine L m
  rw [hcyc, c1, c2] at haff
  rw [Nat.sub_mul]
  omega

/-- `B(chr r (2r)) = 4^r - 3^r`. -/
theorem Bnum_chr_double {r : ℕ} (hr : 0 < r) :
    Bnum r (NormGoal.chr r (2 * r)) = 2 ^ (2 * r) - 3 ^ r := by
  have key := chr_rep (d := r) (r' := 1) (A' := 2) hr one_pos
  have hle : 3 ^ r ≤ 2 ^ (2 * r) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by norm_num) r
  have hqz := q_rep (d := r) (r' := 1) (A' := 2) (by rw [mul_one, mul_comm]; exact hle)
  rw [mul_one, mul_comm r 2] at key hqz
  have hB1 : Bnum 1 (NormGoal.chr 1 2) = 1 := by simp [Bnum, psum]
  rw [key, hB1, mul_one]
  have : ((2 ^ (2 * r) - 3 ^ r : ℕ) : ℤ) = (Sg (2 ^ 2) (3 ^ 1) r : ℤ) := by
    rw [hqz]; norm_num
  exact_mod_cast this.symm

/-- **Bridge corollary.** A positive `T`-cycle of length `L` with `r ≥ 2` odd steps whose
valuation word `v` is `chr r L` (on `range r`) or one move from it must be the trivial cycle:
`L = 2r`, `v = chr r (2r) = (2,…,2)` and `m = 1`. -/
theorem cycle_one_move_christoffel {m L r : ℕ} {v : ℕ → ℕ} (hr : 2 ≤ r)
    (hv1 : ∀ i < r, 1 ≤ v i) (hL : psum v r = L)
    (hodd : ∀ j < L, (T^[j] m % 2 = 1 ↔ ∃ i < r, psum v i = j)) (hcyc : T^[L] m = m)
    (hv : OneMove r (NormGoal.chr r L) v ∨ ∀ j < r, v j = NormGoal.chr r L j) :
    L = 2 * r ∧ (∀ j < r, v j = NormGoal.chr r L j) ∧ m = 1 := by
  have heq := cycle_word_eq hv1 hL hodd hcyc
  have hBpos : 0 < Bnum r v := by
    unfold Bnum
    exact sum_pos' (fun _ _ => Nat.zero_le _) ⟨0, mem_range.mpr (by omega), by positivity⟩
  have hlt : 3 ^ r < 2 ^ L := by
    by_contra h
    rw [Nat.sub_eq_zero_of_le (not_lt.mp h), zero_mul] at heq; omega
  have hq : 3 ^ r + 1 < 2 ^ L := by
    by_contra h
    have := pow_two_eq_three_pow_succ (a := L) (b := r) (by omega) (by omega)
    omega
  have hdiv : (2 ^ L - 3 ^ r) ∣ Bnum r v := ⟨m, by rw [← heq, mul_comm]⟩
  obtain ⟨h1, h2⟩ := (one_move_classification r L hr hq v hv).mp hdiv
  refine ⟨h1, h2, ?_⟩
  rw [Bnum_congr h2, h1, Bnum_chr_double (by omega), ← h1] at heq
  have hqpos : 0 < 2 ^ L - 3 ^ r := by omega
  have : (2 ^ L - 3 ^ r) * m = (2 ^ L - 3 ^ r) * 1 := by rw [heq, mul_one]
  exact Nat.eq_of_mul_eq_mul_left hqpos this

end CollatzSearch.NormBridge

#print axioms CollatzSearch.NormBridge.cycle_word_eq
#print axioms CollatzSearch.NormBridge.Bnum_chr_double
#print axioms CollatzSearch.NormBridge.cycle_one_move_christoffel
