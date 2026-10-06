import Collatz.ProductBound
import Collatz.GoodRotation
import Mathlib.Tactic

/-!
# Max-side ascent product

The maximum-side dual of `ProductBound.descent_product` (Crandall 1978 / Eliahou 1993 style).
If every point of a `T`-orbit segment of length `j` starting at `n` is `≤ M`, each odd step
multiplies by at least `(3M+1)/(2M)`, giving `(3M+1)^{S_j n} n ≤ 2^j T^j(n) M^{S_j n}`.

Consequences for an orbit maximum `M > 0` (`∀ i, T^i M ≤ M`): every prefix satisfies
`(3M+1)^{S_j} ≤ 2^j M^{S_j}` (`max_prefix_product`), hence is strictly light,
`3^{S_j} < 2^j` once `S_j > 0` (`max_prefix_light`); on a cycle with `k = K+1` odd steps in `L`
steps, `(K+1)3^K + M 3^{K+1} ≤ M 2^L`, i.e. `M (2^L - 3^k) ≥ k 3^{k-1}` (`max_lower`).

**Scope.** SIGN-SENSITIVE: the analogue FAILS for `3n-1` (cycle `5 → 7 → 10`,
max `M = 10`, `k = 2`, `L = 3`: `31^2 = 961 > 800` and `6 + 90 = 96 > 80`; see the `example`s at
the end), because the factor is `1 - 1/(3x) < 1` there. It HOLDS for `T_d(x) = (3x+d)/2`, `d > 0`,
so alone it excludes no cycle. Classical-in-spirit dual of Crandall/Eliahou; novelty unclear
(likely folklore).
-/

namespace Collatz
open CollatzProof

/-- **Ascent product.** If `T^i(n) ≤ M` for all `i < j`, then
`(3M+1)^{S_j(n)} · n ≤ 2^j · T^j(n) · M^{S_j(n)}`. (No positivity of `M` is needed.) -/
theorem ascent_product (M : ℕ) : ∀ (j n : ℕ), (∀ i, i < j → T^[i] n ≤ M) →
    (3 * M + 1) ^ oddSteps j n * n ≤ 2 ^ j * T^[j] n * M ^ oddSteps j n := by
  intro j
  induction j with
  | zero => intro n _; simp [oddSteps]
  | succ j ih =>
    intro n hi
    have hnM : n ≤ M := by simpa using hi 0 (by omega)
    have ih' := ih (T n) (fun i hij => by
      have := hi (i + 1) (by omega)
      rwa [Function.iterate_succ_apply] at this)
    set S := oddSteps j (T n)
    set X := T^[j] (T n)
    rw [Function.iterate_succ_apply]
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have h2 : 2 * T n = n := by rw [T_of_even h]; omega
      have hs : oddSteps (j + 1) n = S := by simp [oddSteps, h, S]
      rw [hs]
      calc (3 * M + 1) ^ S * n = (3 * M + 1) ^ S * (2 * T n) := by rw [h2]
        _ = 2 * ((3 * M + 1) ^ S * T n) := by ring
        _ ≤ 2 * (2 ^ j * X * M ^ S) := Nat.mul_le_mul_left 2 ih'
        _ = 2 ^ (j + 1) * X * M ^ S := by ring
    · have h2 : 2 * T n = 3 * n + 1 := by rw [T_of_odd h]; omega
      have hs : oddSteps (j + 1) n = S + 1 := by simp [oddSteps, h, S]
      rw [hs]
      have key : (3 * M + 1) * n ≤ 2 * T n * M := by
        rw [h2]; nlinarith
      calc (3 * M + 1) ^ (S + 1) * n = (3 * M + 1) ^ S * ((3 * M + 1) * n) := by ring
        _ ≤ (3 * M + 1) ^ S * (2 * T n * M) := Nat.mul_le_mul_left _ key
        _ = ((3 * M + 1) ^ S * T n) * (2 * M) := by ring
        _ ≤ (2 ^ j * X * M ^ S) * (2 * M) := Nat.mul_le_mul_right _ ih'
        _ = 2 ^ (j + 1) * X * M ^ (S + 1) := by ring

/-- If `M > 0` is the maximum of its `T`-orbit, then for every `j`,
`(3M+1)^{S_j(M)} ≤ 2^j · M^{S_j(M)}`. -/
theorem max_prefix_product {M : ℕ} (hM : 0 < M) (hmax : ∀ i, T^[i] M ≤ M) (j : ℕ) :
    (3 * M + 1) ^ oddSteps j M ≤ 2 ^ j * M ^ oddSteps j M := by
  have h := ascent_product M j M (fun i _ => hmax i)
  have h' : (3 * M + 1) ^ oddSteps j M * M ≤ (2 ^ j * M ^ oddSteps j M) * M :=
    calc (3 * M + 1) ^ oddSteps j M * M ≤ 2 ^ j * T^[j] M * M ^ oddSteps j M := h
      _ ≤ 2 ^ j * M * M ^ oddSteps j M :=
          Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (hmax j))
      _ = (2 ^ j * M ^ oddSteps j M) * M := by ring
  exact Nat.le_of_mul_le_mul_right h' hM

/-- From the orbit maximum every prefix with at least one odd step is strictly light:
`3^{S_j(M)} < 2^j`. -/
theorem max_prefix_light {M : ℕ} (hM : 0 < M) (hmax : ∀ i, T^[i] M ≤ M) (j : ℕ)
    (hS : 0 < oddSteps j M) : 3 ^ oddSteps j M < 2 ^ j := by
  set S := oddSteps j M
  have h1 : (3 * M) ^ S < (3 * M + 1) ^ S := Nat.pow_lt_pow_left (by omega) (by omega)
  have h2 := max_prefix_product hM hmax j
  rw [mul_pow] at h1
  have : 3 ^ S * M ^ S < 2 ^ j * M ^ S := lt_of_lt_of_le h1 h2
  exact Nat.lt_of_mul_lt_mul_right this

/-- Natural-number Bernoulli: `a^{K+1} + (K+1) a^K ≤ (a+1)^{K+1}`. -/
theorem bernoulli_nat_succ (a : ℕ) : ∀ K : ℕ, a ^ (K + 1) + (K + 1) * a ^ K ≤ (a + 1) ^ (K + 1) := by
  intro K
  induction K with
  | zero => simp
  | succ K ih =>
    calc a ^ (K + 1 + 1) + (K + 1 + 1) * a ^ (K + 1)
        ≤ (a + 1) * (a ^ (K + 1) + (K + 1) * a ^ K) := by
          have : a ^ (K + 1) = a * a ^ K := by ring
          rw [this, pow_succ, this]; nlinarith [Nat.zero_le (a ^ K), Nat.zero_le a]
      _ ≤ (a + 1) * (a + 1) ^ (K + 1) := Nat.mul_le_mul_left _ ih
      _ = (a + 1) ^ (K + 1 + 1) := by ring

/-- **Max lower bound.** If `M > 0` is the maximum of its `T`-orbit and `S_L(M) = K+1`, then
`(K+1)·3^K + M·3^{K+1} ≤ M·2^L`. (Meaningful when `T^L M = M`; the cycle hypothesis is not
needed for the inequality itself.) -/
theorem max_lower {M L K : ℕ} (hM : 0 < M) (hmax : ∀ i, T^[i] M ≤ M)
    (hk : oddSteps L M = K + 1) : (K + 1) * 3 ^ K + M * 3 ^ (K + 1) ≤ M * 2 ^ L := by
  have h := max_prefix_product hM hmax L
  rw [hk] at h
  have hb := bernoulli_nat_succ (3 * M) K
  have hMK : 0 < M ^ K := pow_pos hM K
  have : ((K + 1) * 3 ^ K + M * 3 ^ (K + 1)) * M ^ K ≤ (M * 2 ^ L) * M ^ K :=
    calc ((K + 1) * 3 ^ K + M * 3 ^ (K + 1)) * M ^ K
        = (3 * M) ^ (K + 1) + (K + 1) * (3 * M) ^ K := by rw [mul_pow, mul_pow]; ring
      _ ≤ (3 * M + 1) ^ (K + 1) := hb
      _ ≤ 2 ^ L * M ^ (K + 1) := h
      _ = (M * 2 ^ L) * M ^ K := by ring
  exact Nat.le_of_mul_le_mul_right this hMK

/-- **Two-sided cycle corridor.** On a `T`-cycle `T^L x = x` with orbit minimum `m = T^a x > 0`
and orbit maximum `M = T^b x`, with the common `k = S_L(x)`:
`2^L m^k ≤ (3m+1)^k` and `(3M+1)^k ≤ 2^L M^k`. -/
theorem cycle_sandwich {x L a b : ℕ} (h : T^[L] x = x) (hm : 0 < T^[a] x)
    (hmin : ∀ i, T^[a] x ≤ T^[i] (T^[a] x)) (hmax : ∀ i, T^[i] (T^[b] x) ≤ T^[b] x) :
    2 ^ L * (T^[a] x) ^ oddSteps L x ≤ (3 * T^[a] x + 1) ^ oddSteps L x ∧
    (3 * T^[b] x + 1) ^ oddSteps L x ≤ 2 ^ L * (T^[b] x) ^ oddSteps L x := by
  have hper : ∀ c, T^[L] (T^[c] x) = T^[c] x := fun c => by
    rw [← Function.iterate_add_apply, add_comm, Function.iterate_add_apply, h]
  have hM : 0 < T^[b] x := lt_of_lt_of_le hm (by
    have := hmax a
    have hmb := hmin b
    rw [← Function.iterate_add_apply] at this hmb
    calc T^[a] x ≤ T^[b + a] x := hmb
      _ = T^[a + b] x := by rw [add_comm]
      _ ≤ T^[b] x := this)
  refine ⟨?_, ?_⟩
  · have := cycle_product_bound hm (hper a) hmin
    rwa [oddSteps_rotate h] at this
  · have := max_prefix_product hM hmax L
    rwa [oddSteps_rotate h] at this

/-- Non-vacuity numbers on the trivial cycle `1 ↔ 2` (max `M = 2`, `k = 1`, `L = 2`): `7 ≤ 8`. -/
example : 1 * 3 ^ 0 + 2 * 3 ^ 1 ≤ 2 * 2 ^ 2 := by norm_num
/-- The analogue for the `3n-1` cycle `5 → 7 → 10` (max 10, k = 2, L = 3) FAILS:
the sign of `+1` is used. -/
example : ¬ (2 * 3 ^ 1 + 10 * 3 ^ 2 ≤ 10 * 2 ^ 3) := by norm_num
/-- Same `3n-1` cycle: the prefix product `(3M+1)^k ≤ 2^L M^k` fails (`961 > 800`). -/
example : ¬ ((3 * 10 + 1) ^ 2 ≤ 2 ^ 3 * 10 ^ 2) := by norm_num

end Collatz

#print axioms Collatz.ascent_product
#print axioms Collatz.max_prefix_product
#print axioms Collatz.max_prefix_light
#print axioms Collatz.bernoulli_nat_succ
#print axioms Collatz.max_lower
#print axioms Collatz.cycle_sandwich
