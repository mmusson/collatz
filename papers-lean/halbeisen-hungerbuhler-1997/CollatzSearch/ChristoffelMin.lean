import CollatzSearch.GoodRotation
import Mathlib.Tactic

/-!
# Christoffel bound for cycle minima

**UNCONDITIONAL. KNOWN THEOREM: Halbeisen–Hungerbühler 1997 (Acta Arith. 78, Thm 3, upper
half); Christoffel-word extremality re-derived by Fernández–Ibáñez 2026.** This file is (to our
knowledge) its first formalization.  **NOT progress on `no_nontrivial_cycles`, which remains OPEN.**

For a positive `T`-cycle with minimum `m`, length `L`, and `k` odd steps (`k = oddSteps L m`),
  `m · (2^L − 3^k) ≤ chr L k = Σ_{i<k} 3^{k−1−i} · 2^{⌊iL/k⌋}`.
The right side is the Böhm–Sontacchi sum of the lower Christoffel word of slope `k/L`.  This
sharpens the `GoodRotation` Crandall/Eliahou bound `(m+1)(2^L−3^k)·2 ≤ (L−k)2^L`
(`min_bound_of_good_rotation`) by about 18–20% numerically (e.g. `(65,41)`: `867.1` vs `1052.9`).

* `bsum_affine` (positional Böhm–Sontacchi): `2^j T^j n = 3^{S_j(n)} n + bsum j n`, where
  `bsum` adds `2^j` (after multiplying by 3) at each odd step `j`.
* `bsum_le_chrG` (dominance): if `k·i ≤ L·S_i(n)` for all `i < j`, then `bsum j n ≤ chrG(S_j(n))`.
* `exists_linear_rotation` (gas station, linear potential `L·S_i − k·i`): some rotation point
  `T^r x`, `r < L`, satisfies `k·j ≤ L·S_j(T^r x)` for every `j`.
* `cycle_min_le_chr`: the main bound; `no_cycle_sig_above`: per-signature exclusion form.
-/

namespace CollatzSearch
open CollatzProof

/-- Positional Böhm–Sontacchi sum: `bsum 0 n = 0`, and at step `j` it becomes
`3·bsum j n + 2^j` if `T^j n` is odd, else stays `bsum j n`. -/
def bsum : ℕ → ℕ → ℕ
  | 0, _ => 0
  | j+1, n => if T^[j] n % 2 = 1 then 3 * bsum j n + 2 ^ j else bsum j n

/-- Christoffel partial sum: `chrG L k p = Σ_{i<p} 3^{p−1−i} 2^{⌊iL/k⌋}`. -/
def chrG (L k : ℕ) : ℕ → ℕ
  | 0 => 0
  | p+1 => 3 * chrG L k p + 2 ^ (p * L / k)

/-- `chr L k = Σ_{i<k} 3^{k−1−i} 2^{⌊iL/k⌋}`, the Böhm–Sontacchi sum of the lower
Christoffel word with `k` ones among `L` letters. -/
def chr (L k : ℕ) : ℕ := chrG L k k

/-- Sanity: `⌊8i/5⌋` for `i<5` are `0,1,3,4,6` give `81+54+72+48+64 = 319`. -/
example : chr 8 5 = 319 := by decide
/-- Sanity: the trivial cycle `1 → 2 → 1` (`L=2,k=1,D=1,m=1`) makes the bound tight. -/
example : chr 2 1 = 1 := by decide
/-- Sanity: `chr 8 5 ≤ (L−k)2^{L−1}` at `(8,5)` (the general comparison is numerics only). -/
example : chr 8 5 ≤ (8 - 5) * 2 ^ (8 - 1) := by decide

/-- Last-step recursion for `oddSteps`: `S_{j+1}(n) = S_j(n) + [T^j n odd]`. -/
theorem oddSteps_succ_last (j n : ℕ) : oddSteps (j+1) n = oddSteps j n + T^[j] n % 2 := by
  rw [oddSteps_add]; simp [oddSteps]

/-- **Positional Böhm–Sontacchi identity**: `2^j · T^j(n) = 3^{S_j(n)} · n + bsum j n`. -/
theorem bsum_affine (j n : ℕ) : 2 ^ j * T^[j] n = 3 ^ oddSteps j n * n + bsum j n := by
  induction j with
  | zero => simp [oddSteps, bsum]
  | succ j ih =>
    rw [Function.iterate_succ_apply', oddSteps_succ_last, pow_succ]
    rcases Nat.mod_two_eq_zero_or_one (T^[j] n) with h | h
    · have h2 : 2 * T (T^[j] n) = T^[j] n := by rw [T_of_even h]; omega
      simp only [bsum, h, add_zero]; simp only [zero_ne_one, ite_false]
      rw [mul_assoc, h2, ih]
    · have h2 : 2 * T (T^[j] n) = 3 * T^[j] n + 1 := by rw [T_of_odd h]; omega
      simp only [bsum, h, ite_true]
      rw [mul_assoc, h2, pow_succ]
      calc 2 ^ j * (3 * T^[j] n + 1) = 3 * (2 ^ j * T^[j] n) + 2 ^ j := by ring
        _ = _ := by rw [ih]; ring

/-- **Dominance.** If `k > 0` and every prefix `i < j` satisfies `k·i ≤ L·S_i(n)`, then
`bsum j n ≤ chrG L k (S_j(n))`: each odd step at time `j` with `P` earlier odd steps has
`j ≤ ⌊PL/k⌋`. -/
theorem bsum_le_chrG {L k : ℕ} (hk : 0 < k) : ∀ (j n : ℕ), (∀ i < j, k * i ≤ L * oddSteps i n) →
    bsum j n ≤ chrG L k (oddSteps j n) := by
  intro j n
  induction j with
  | zero => intro _; simp [bsum, oddSteps, chrG]
  | succ j ih =>
    intro hyp
    have IH := ih (fun i hi => hyp i (by omega))
    rw [oddSteps_succ_last]
    rcases Nat.mod_two_eq_zero_or_one (T^[j] n) with h | h
    · simp only [bsum, h, add_zero, zero_ne_one, ite_false]; exact IH
    · simp only [bsum, h, ite_true, chrG]
      have hj : j ≤ oddSteps j n * L / k := by
        rw [Nat.le_div_iff_mul_le hk]
        have := hyp j (by omega); linarith [mul_comm k j, mul_comm L (oddSteps j n)]
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hj
      omega

/-- **Gas-station rotation, linear threshold.** On a `T`-cycle of length `L > 0` with
`k = S_L(x)` odd steps there is `r < L` such that every prefix of the orbit of `T^r x`
satisfies `k·j ≤ L·S_j(T^r x)` (minimise the `L`-periodic potential `L·S_i − k·i`). -/
theorem exists_linear_rotation {x L : ℕ} (hL : 0 < L) (h : T^[L] x = x) :
    ∃ r < L, ∀ j, oddSteps L x * j ≤ L * oddSteps j (T^[r] x) := by
  set k := oddSteps L x
  let f : ℕ → ℤ := fun i => (L : ℤ) * oddSteps i x - k * i
  have hper : ∀ s q, f (s + L * q) = f s := by
    intro s q
    induction q with
    | zero => simp
    | succ q ih =>
      rw [show s + L * (q+1) = (s + L * q) + L by ring]
      simp only [f] at ih ⊢
      rw [oddSteps_add_period h]; push_cast
      have hkd : ((oddSteps L x : ℕ) : ℤ) = (k : ℤ) := rfl
      rw [hkd]; push_cast at ih; linarith
  have hne : (Finset.range L).Nonempty := ⟨0, by simp; omega⟩
  obtain ⟨r, hr, hmin⟩ := Finset.exists_min_image _ f hne
  simp only [Finset.mem_range] at hr
  refine ⟨r, hr, fun j => ?_⟩
  have e1 : f (r + j) = f ((r + j) % L) := by
    conv_lhs => rw [← Nat.mod_add_div (r + j) L]
    exact hper _ _
  have key : f r ≤ f (r + j) := by
    rw [e1]; exact hmin _ (by simp; exact Nat.mod_lt _ hL)
  have e3 := oddSteps_add r j x
  simp only [f] at key
  rw [e3] at key; push_cast at key
  have : (k:ℤ) * j ≤ L * oddSteps j (T^[r] x) := by nlinarith
  exact_mod_cast this

/-- **Halbeisen–Hungerbühler 1997, Thm 3 (upper bound); first formalization.** If `m > 0` is the
minimum of a `T`-cycle of length `L > 0` with `k` odd steps, then
`m·(2^L − 3^k) ≤ Σ_{i<k} 3^{k−1−i} 2^{⌊iL/k⌋}`. Known; NOT Goal progress. -/
theorem cycle_min_le_chr {m L : ℕ} (hm : 0 < m) (hL : 0 < L) (h : T^[L] m = m)
    (hmin : ∀ i, m ≤ T^[i] m) :
    m * (2 ^ L - 3 ^ oddSteps L m) ≤ chr L (oddSteps L m) := by
  set k := oddSteps L m with hkdef
  obtain ⟨r, _, hr⟩ := exists_linear_rotation hL h
  set y := T^[r] m with hy
  have hyc : T^[L] y = y := by
    rw [hy, ← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, h]
  have hky : oddSteps L y = k := oddSteps_rotate h r
  have hk : 0 < k := oddSteps_pos_of_cycle hm hL h
  have hA := bsum_affine L y
  rw [hyc, hky] at hA
  have hB := bsum_le_chrG (L := L) hk L y (fun i _ => hr i)
  rw [hky] at hB
  have hmy : m ≤ y := hmin r
  have hlt : 3 ^ k < 2 ^ L := three_pow_lt_two_pow_of_cycle hm hL h
  have hyD : y * (2 ^ L - 3 ^ k) = bsum L y := by
    rw [Nat.mul_sub, mul_comm y (2^L), hA, mul_comm y]; omega
  calc m * (2 ^ L - 3 ^ k) ≤ y * (2 ^ L - 3 ^ k) := Nat.mul_le_mul_right _ hmy
    _ = bsum L y := hyD
    _ ≤ chr L k := hB

/-- **Per-signature exclusion.** If `chr L k < (X+1)(2^L − 3^k)` for the signature `(L,k)` of
a `T`-cycle, its minimum is at most `X`. -/
theorem no_cycle_sig_above {m L X : ℕ} (hm : 0 < m) (hL : 0 < L) (h : T^[L] m = m)
    (hmin : ∀ i, m ≤ T^[i] m)
    (hc : chr L (oddSteps L m) < (X + 1) * (2 ^ L - 3 ^ oddSteps L m)) : m ≤ X := by
  by_contra hX
  push Not at hX
  have := cycle_min_le_chr hm hL h hmin
  have := Nat.mul_le_mul_right (2 ^ L - 3 ^ oddSteps L m) (show X + 1 ≤ m by omega)
  omega

/-- Sanity: the theorem applied to the trivial cycle `1 → 2 → 1`. -/
example : 1 * (2 ^ 2 - 3 ^ oddSteps 2 1) ≤ chr 2 (oddSteps 2 1) :=
  cycle_min_le_chr (by norm_num) (by norm_num) (by decide) (fun i => by
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply']; exact T_pos (by omega))

end CollatzSearch

#print axioms CollatzSearch.bsum_affine
#print axioms CollatzSearch.bsum_le_chrG
#print axioms CollatzSearch.exists_linear_rotation
#print axioms CollatzSearch.cycle_min_le_chr
#print axioms CollatzSearch.no_cycle_sig_above
