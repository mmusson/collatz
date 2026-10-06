import CollatzSearch.Descent
import Mathlib.Tactic

/-!
# Residue-tree descent sieve (kernel-checkable)

A node `(j, r, a, c)` is `Valid` if `T^j (r + 2^j y) = a y + c` for every `y` (Terras'
affine form on the residue class `r mod 2^j`).  The root `(0, 0, 1, 0)` is valid, and each of the
two children (`r` or `r + 2^j` mod `2^{j+1}`) is valid with `(a, c)` updated by one `T`-step
(`valid_child_even`, `valid_child_odd`).  A node with `a < 2^j` and `c < r` descends for the whole
class (`valid_prune`).  `sv fuel N lo d f bits r a c pw` walks the tree (`pw = 2^j`) to remaining
depth `d`, first following the `f` forced low bits of `bits`, prunes where possible, and at the
leaves checks the `N` numbers `r + 2^j y` (`y < N`) individually, starting from `T^j n = a y + c`
(`leafOK`, using `descends` from `Descent.lean`).

* `sv_sound`: a successful run proves descent for every `y < N·2^d` with the forced low bits.
* `descRange_of_roots`: if the sieve succeeds for all `2^f` patterns, `DescRange lo (2^K N)`.
* `min_orbit_ge_of_descRange`: `DescRange 2 X` ⇒ the minimum `m > 1` of a `T`-orbit is `≥ X`.

Classical (the Oliveira e Silva-style class sieve); it gains only a constant factor over direct
enumeration.  Instances: `Sieve24Part0..7`, `Sieve24` (`X = 2^24`).
-/

namespace CollatzSearch
open CollatzProof

/-- Node invariant: `T^j (r + 2^j y) = a y + c` for all `y`. -/
def Valid (j r a c : ℕ) : Prop := ∀ y, T^[j] (r + 2^j * y) = a * y + c

theorem valid_root : Valid 0 0 1 0 := by intro y; simp

theorem valid_child_even {j r a c b : ℕ} (hv : Valid j r a c) (h : (c + a*b) % 2 = 0) :
    Valid (j+1) (r + b*2^j) a ((c + a*b)/2) := by
  intro y
  have e : r + b*2^j + 2^(j+1)*y = r + 2^j*(b + 2*y) := by rw [pow_succ]; ring
  rw [e, Function.iterate_succ_apply', hv]
  have e2 : a * (b + 2*y) + c = 2*(a*y) + (c + a*b) := by ring
  rw [e2]; unfold T
  have hp : (2*(a*y) + (c + a*b)) % 2 = 0 := by omega
  simp only [hp, ↓reduceIte]; omega

theorem valid_child_odd {j r a c b : ℕ} (hv : Valid j r a c) (h : (c + a*b) % 2 = 1) :
    Valid (j+1) (r + b*2^j) (3*a) ((3*(c + a*b)+1)/2) := by
  intro y
  have e : r + b*2^j + 2^(j+1)*y = r + 2^j*(b + 2*y) := by rw [pow_succ]; ring
  rw [e, Function.iterate_succ_apply', hv]
  have e2 : a * (b + 2*y) + c = 2*(a*y) + (c + a*b) := by ring
  rw [e2, mul_assoc]; unfold T
  have hp : ¬ (2*(a*y) + (c + a*b)) % 2 = 0 := by omega
  simp only [hp, ↓reduceIte]; omega

/-- Prune: if `a < 2^j` and `c < r` then every `n ≡ r (mod 2^j)` descends at step `j`. -/
theorem valid_prune {j r a c : ℕ} (hv : Valid j r a c) (ha : a < 2^j) (hc : c < r) (y : ℕ) :
    T^[j] (r + 2^j*y) < r + 2^j*y := by
  rw [hv]; have := Nat.mul_le_mul_right y ha.le; nlinarith

/-- Leaf check for one `y`: `n = r + pw·y` is below `lo`, or `T^j n = a y + c < n`, or some
further iterate of `a y + c` drops below `n`. -/
def leafOK (fuel lo r a c pw y : ℕ) : Bool :=
  Nat.blt (r + pw*y) lo || Nat.blt (a*y + c) (r + pw*y) || descends (r + pw*y) fuel (a*y + c)

def leafAll (fuel lo r a c pw : ℕ) : ℕ → Bool
  | 0 => true
  | y + 1 => leafAll fuel lo r a c pw y && leafOK fuel lo r a c pw y

theorem leafAll_sound {fuel lo r a c pw : ℕ} : ∀ N, leafAll fuel lo r a c pw N = true →
    ∀ y < N, leafOK fuel lo r a c pw y = true := by
  intro N; induction N with
  | zero => intro _ y hy; omega
  | succ N ih =>
    intro h y hy
    simp only [leafAll, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp hy with hy | rfl
    · exact ih h.1 y hy
    · exact h.2

/-- The residue-tree sieve.  `d` = remaining depth, `f` = number of forced low bits of `y`
still to follow (their values are the low bits of `bits`). -/
def sv (fuel N lo : ℕ) : ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, r, a, c, pw => (Nat.blt a pw && Nat.blt c r) || leafAll fuel lo r a c pw N
  | d + 1, f, bits, r, a, c, pw => (Nat.blt a pw && Nat.blt c r) ||
      (match f with
        | 0 =>
          (bif c % 2 == 0 then sv fuel N lo d 0 0 r a (c/2) (pw*2)
            else sv fuel N lo d 0 0 r (3*a) ((3*c+1)/2) (pw*2)) &&
          (bif (c + a) % 2 == 0 then sv fuel N lo d 0 0 (r + pw) a ((c + a)/2) (pw*2)
            else sv fuel N lo d 0 0 (r + pw) (3*a) ((3*(c+a)+1)/2) (pw*2))
        | f + 1 =>
          bif bits % 2 == 0 then
            (bif c % 2 == 0 then sv fuel N lo d f (bits/2) r a (c/2) (pw*2)
              else sv fuel N lo d f (bits/2) r (3*a) ((3*c+1)/2) (pw*2))
          else
            (bif (c + a) % 2 == 0 then sv fuel N lo d f (bits/2) (r + pw) a ((c + a)/2) (pw*2)
              else sv fuel N lo d f (bits/2) (r + pw) (3*a) ((3*(c+a)+1)/2) (pw*2)))

theorem leaf_sound {fuel lo j r a c y : ℕ} (hv : Valid j r a c)
    (h : leafOK fuel lo r a c (2^j) y = true) (hlo : lo ≤ r + 2^j*y) :
    ∃ i, T^[i] (r + 2^j*y) < r + 2^j*y := by
  simp only [leafOK, Bool.or_eq_true, Nat.blt_eq] at h
  rcases h with (h | h) | h
  · omega
  · exact ⟨j, by rw [hv]; exact h⟩
  · obtain ⟨i, hi⟩ := descends_sound _ fuel _ h
    exact ⟨i + j, by rw [Function.iterate_add_apply, hv]; exact hi⟩

theorem sv_sound (fuel N lo : ℕ) : ∀ d f bits j r a c, Valid j r a c →
    sv fuel N lo d f bits r a c (2^j) = true →
    ∀ y, y < N * 2^d → y % 2^f = bits % 2^f → lo ≤ r + 2^j*y →
    ∃ i, T^[i] (r + 2^j*y) < r + 2^j*y := by
  intro d
  induction d with
  | zero =>
    intro f bits j r a c hv h y hy _ hlo
    simp only [sv, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    rcases h with ⟨ha, hc⟩ | h
    · exact ⟨j, valid_prune hv ha hc y⟩
    · exact leaf_sound hv (leafAll_sound N h y (by simpa using hy)) hlo
  | succ d ih =>
    intro f bits j r a c hv h y hy hbits hlo
    simp only [sv, Bool.or_eq_true, Bool.and_eq_true, Nat.blt_eq] at h
    rcases h with ⟨ha, hc⟩ | h
    · exact ⟨j, valid_prune hv ha hc y⟩
    -- decompose y = b + 2 y'
    have hy' : y / 2 < N * 2^d := by
      rw [pow_succ, ← mul_assoc] at hy; omega
    have hdecomp : r + 2^j*y = (r + (y % 2)*2^j) + 2^(j+1)*(y/2) := by
      rw [pow_succ]
      have := Nat.mod_add_div y 2
      calc r + 2^j*y = r + 2^j*(y%2 + 2*(y/2)) := by rw [this]
        _ = _ := by ring
    have hpw : 2^j * 2 = 2^(j+1) := (pow_succ 2 j).symm
    rw [hdecomp]
    -- the child check for bit b
    have key : ∀ b, b = y % 2 → ∀ f' bits',
        (y/2) % 2^f' = bits' % 2^f' →
        (bif (c + a*b) % 2 == 0 then sv fuel N lo d f' bits' (r + b*2^j) a ((c + a*b)/2) (2^(j+1))
          else sv fuel N lo d f' bits' (r + b*2^j) (3*a) ((3*(c + a*b)+1)/2) (2^(j+1))) = true →
        ∃ i, T^[i] ((r + b*2^j) + 2^(j+1)*(y/2)) < (r + b*2^j) + 2^(j+1)*(y/2) := by
      intro b hb f' bits' hb' hc
      rcases Nat.mod_two_eq_zero_or_one (c + a*b) with h2 | h2
      · rw [h2] at hc; simp only [Bool.cond_true, beq_self_eq_true] at hc
        exact ih f' bits' (j+1) _ _ _ (valid_child_even hv h2) hc (y/2) hy' hb'
          (by rw [hb, ← hdecomp]; exact hlo)
      · rw [h2] at hc; simp only [Bool.cond_false, show ((1:ℕ) == 0) = false from rfl] at hc
        exact ih f' bits' (j+1) _ _ _ (valid_child_odd hv h2) hc (y/2) hy' hb'
          (by rw [hb, ← hdecomp]; exact hlo)
    rcases f with _ | f
    · simp only [Bool.and_eq_true] at h
      rcases Nat.mod_two_eq_zero_or_one y with hb | hb
      · have := key 0 hb.symm 0 0 (by rw [pow_zero]; omega) (by simpa [hpw] using h.1)
        rwa [hb]
      · have := key 1 hb.symm 0 0 (by rw [pow_zero]; omega) (by simpa [hpw] using h.2)
        rwa [hb]
    · have hm := hbits
      rw [pow_succ, mul_comm, Nat.mod_mul, Nat.mod_mul] at hm
      have hb2 : y % 2 = bits % 2 := by omega
      have hf : (y/2) % 2^f = (bits/2) % 2^f := by omega
      rcases Nat.mod_two_eq_zero_or_one y with hb | hb
      · rw [hb] at hb2
        rw [← hb2] at h; simp only [Bool.cond_true, beq_self_eq_true] at h
        have := key 0 hb.symm f (bits/2) hf (by simpa [hpw] using h)
        rwa [hb]
      · rw [hb] at hb2
        rw [← hb2] at h; simp only [Bool.cond_false, show ((1:ℕ) == 0) = false from rfl] at h
        have := key 1 hb.symm f (bits/2) hf (by simpa [hpw] using h)
        rwa [hb]

/-- Conjunction of the sieve over the forced-bit patterns `bits ∈ [start, start + cnt)`. -/
def svRange (fuel N lo K f start : ℕ) : ℕ → Bool
  | 0 => true
  | cnt + 1 => svRange fuel N lo K f start cnt && sv fuel N lo K f (start + cnt) 0 1 0 1

/-- `RootsOK … s e`: the sieve succeeds from the root for every forced pattern in `[s, e)`. -/
def RootsOK (fuel N lo K f s e : ℕ) : Prop :=
  ∀ bits, s ≤ bits → bits < e → sv fuel N lo K f bits 0 1 0 1 = true

theorem rootsOK_nil (fuel N lo K f e : ℕ) : RootsOK fuel N lo K f e e :=
  fun _ h1 h2 => absurd h2 (by omega)

theorem svRange_sound {fuel N lo K f start : ℕ} : ∀ cnt, svRange fuel N lo K f start cnt = true →
    ∀ bits, start ≤ bits → bits < start + cnt → sv fuel N lo K f bits 0 1 0 1 = true := by
  intro cnt; induction cnt with
  | zero => intro _ b h1 h2; omega
  | succ cnt ih =>
    intro h b h1 h2
    simp only [svRange, Bool.and_eq_true] at h
    rcases Nat.lt_succ_iff_lt_or_eq.mp (show b < (start + cnt) + 1 by omega) with hb | hb
    · exact ih h.1 b h1 hb
    · rw [hb]; exact h.2

theorem rootsOK_cons {fuel N lo K f s cnt e : ℕ} (h : svRange fuel N lo K f s cnt = true)
    (h2 : RootsOK fuel N lo K f (s + cnt) e) : RootsOK fuel N lo K f s e := by
  intro b h1 hb
  by_cases hc : b < s + cnt
  · exact svRange_sound cnt h b h1 hc
  · exact h2 b (by omega) hb

theorem rootsOK_append {fuel N lo K f s m e : ℕ} (h1 : RootsOK fuel N lo K f s m)
    (h2 : RootsOK fuel N lo K f m e) : RootsOK fuel N lo K f s e := by
  intro b hb1 hb2
  by_cases hc : b < m
  · exact h1 b hb1 hc
  · exact h2 b (by omega) hb2

/-- **Sieve soundness at the root.** If the sieve succeeds for all `2^f` forced patterns, then
every `m ∈ [lo, 2^K N)` has a `T`-iterate below `m`. -/
theorem descRange_of_roots {fuel N lo K f : ℕ} (h : RootsOK fuel N lo K f 0 (2^f)) :
    DescRange lo (2^K * N) := by
  intro m h1 h2
  have hs := h (m % 2^f) (Nat.zero_le _) (Nat.mod_lt _ (by positivity))
  have := sv_sound fuel N lo K f (m % 2^f) 0 0 1 0 valid_root hs m
    (by rw [mul_comm]; exact h2) (Nat.mod_mod _ _).symm (by simpa using h1)
  simpa using this

/-- If every `m ∈ [2, X)` descends, the minimum `m > 1` of a `T`-orbit is `≥ X`. -/
theorem min_orbit_ge_of_descRange {X m : ℕ} (hD : DescRange 2 X) (hm : 1 < m)
    (hmin : ∀ j, m ≤ T^[j] m) : X ≤ m := by
  by_contra hc
  obtain ⟨j, hj⟩ := hD m (by omega) (by omega)
  exact absurd (hmin j) (by omega)

end CollatzSearch

#print axioms CollatzSearch.valid_child_even
#print axioms CollatzSearch.valid_child_odd
#print axioms CollatzSearch.valid_prune
#print axioms CollatzSearch.leaf_sound
#print axioms CollatzSearch.sv_sound
#print axioms CollatzSearch.descRange_of_roots
#print axioms CollatzSearch.min_orbit_ge_of_descRange
