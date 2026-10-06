import CollatzSearch.Affine

/-!
# Kernel-verified descent below `2 + 2^17`

Every `m` with `2 ≤ m < 2 + 2^17` has a `T`-iterate strictly below `m`.  This is checked by
the Lean kernel (`decide +kernel`, no `native_decide`) with a fuel-bounded search
(`descends`, fuel 200; the maximal `T`-stopping time below `2^17` is 135).  The range is
split into 32 blocks of `2^12` numbers, each its own declaration (the kernel cost of a
single `2^17` block was superlinear: 601 s, versus ~1 s per `2^12` block).  Consequence
`min_orbit_ge`: the minimum `m > 1` of a `T`-orbit satisfies `m ≥ 2^17`.
Classical: the literature has verified far larger ranges (`> 2^68`).
-/

namespace CollatzSearch
open CollatzProof

/-- Bool-friendly copy of `T` for kernel evaluation. -/
def Tb (x : ℕ) : ℕ := bif x % 2 == 0 then x / 2 else (3 * x + 1) / 2

theorem Tb_eq (x : ℕ) : Tb x = T x := by
  unfold Tb T
  by_cases h : x % 2 = 0 <;> simp [h]

/-- Fuel-bounded search: some `T`-iterate (≥ 1 step) of `x` is `< m`. -/
def descends (m : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, x => Nat.blt (Tb x) m || descends m f (Tb x)

theorem descends_sound (m : ℕ) : ∀ f x, descends m f x = true → ∃ j, T^[j] x < m := by
  intro f
  induction f with
  | zero => intro x h; simp [descends] at h
  | succ f ih =>
    intro x h
    simp only [descends, Bool.or_eq_true, Nat.blt_eq, Tb_eq] at h
    rcases h with h | h
    · exact ⟨1, by simpa using h⟩
    · obtain ⟨j, hj⟩ := ih _ h
      exact ⟨j + 1, by rwa [Function.iterate_succ_apply]⟩

/-- Checks every `m ∈ [lo, lo + 2^d)` by binary splitting (recursion depth `d`). -/
def checkBlock (fuel lo : ℕ) : ℕ → Bool
  | 0 => descends lo fuel lo
  | d + 1 => checkBlock fuel lo d && checkBlock fuel (lo + 2 ^ d) d

theorem checkBlock_sound (fuel : ℕ) : ∀ d lo, checkBlock fuel lo d = true →
    ∀ m, lo ≤ m → m < lo + 2 ^ d → ∃ j, T^[j] m < m := by
  intro d
  induction d with
  | zero =>
    intro lo h m h1 h2
    obtain rfl : m = lo := by simp at h2; omega
    exact descends_sound m fuel m h
  | succ d ih =>
    intro lo h m h1 h2
    simp only [checkBlock, Bool.and_eq_true] at h
    rw [pow_succ] at h2
    by_cases hm : m < lo + 2 ^ d
    · exact ih lo h.1 m h1 hm
    · exact ih (lo + 2 ^ d) h.2 m (by omega) (by omega)

/-- `DescRange lo hi`: every `m` with `lo ≤ m < hi` has some `T`-iterate below `m`. -/
def DescRange (lo hi : ℕ) : Prop := ∀ m, lo ≤ m → m < hi → ∃ j, T^[j] m < m

theorem descRange_nil (hi : ℕ) : DescRange hi hi := fun m h1 h2 => absurd h2 (by omega)

theorem descRange_cons {fuel lo d hi : ℕ} (h : checkBlock fuel lo d = true)
    (h2 : DescRange (lo + 2 ^ d) hi) : DescRange lo hi := by
  intro m h1 hm
  by_cases hc : m < lo + 2 ^ d
  · exact checkBlock_sound fuel d lo h m h1 hc
  · exact h2 m (by omega) hm

theorem descBlock_0 : checkBlock 200 2 12 = true := by decide +kernel
theorem descBlock_1 : checkBlock 200 4098 12 = true := by decide +kernel
theorem descBlock_2 : checkBlock 200 8194 12 = true := by decide +kernel
theorem descBlock_3 : checkBlock 200 12290 12 = true := by decide +kernel
theorem descBlock_4 : checkBlock 200 16386 12 = true := by decide +kernel
theorem descBlock_5 : checkBlock 200 20482 12 = true := by decide +kernel
theorem descBlock_6 : checkBlock 200 24578 12 = true := by decide +kernel
theorem descBlock_7 : checkBlock 200 28674 12 = true := by decide +kernel
theorem descBlock_8 : checkBlock 200 32770 12 = true := by decide +kernel
theorem descBlock_9 : checkBlock 200 36866 12 = true := by decide +kernel
theorem descBlock_10 : checkBlock 200 40962 12 = true := by decide +kernel
theorem descBlock_11 : checkBlock 200 45058 12 = true := by decide +kernel
theorem descBlock_12 : checkBlock 200 49154 12 = true := by decide +kernel
theorem descBlock_13 : checkBlock 200 53250 12 = true := by decide +kernel
theorem descBlock_14 : checkBlock 200 57346 12 = true := by decide +kernel
theorem descBlock_15 : checkBlock 200 61442 12 = true := by decide +kernel
theorem descBlock_16 : checkBlock 200 65538 12 = true := by decide +kernel
theorem descBlock_17 : checkBlock 200 69634 12 = true := by decide +kernel
theorem descBlock_18 : checkBlock 200 73730 12 = true := by decide +kernel
theorem descBlock_19 : checkBlock 200 77826 12 = true := by decide +kernel
theorem descBlock_20 : checkBlock 200 81922 12 = true := by decide +kernel
theorem descBlock_21 : checkBlock 200 86018 12 = true := by decide +kernel
theorem descBlock_22 : checkBlock 200 90114 12 = true := by decide +kernel
theorem descBlock_23 : checkBlock 200 94210 12 = true := by decide +kernel
theorem descBlock_24 : checkBlock 200 98306 12 = true := by decide +kernel
theorem descBlock_25 : checkBlock 200 102402 12 = true := by decide +kernel
theorem descBlock_26 : checkBlock 200 106498 12 = true := by decide +kernel
theorem descBlock_27 : checkBlock 200 110594 12 = true := by decide +kernel
theorem descBlock_28 : checkBlock 200 114690 12 = true := by decide +kernel
theorem descBlock_29 : checkBlock 200 118786 12 = true := by decide +kernel
theorem descBlock_30 : checkBlock 200 122882 12 = true := by decide +kernel
theorem descBlock_31 : checkBlock 200 126978 12 = true := by decide +kernel

/-- Verified: every `m` with `2 ≤ m < 2 + 2^17` descends below itself under `T`. -/
theorem descRange_17 : DescRange 2 (2 + 2 ^ 17) :=
  descRange_cons descBlock_0 <|
  descRange_cons descBlock_1 <|
  descRange_cons descBlock_2 <|
  descRange_cons descBlock_3 <|
  descRange_cons descBlock_4 <|
  descRange_cons descBlock_5 <|
  descRange_cons descBlock_6 <|
  descRange_cons descBlock_7 <|
  descRange_cons descBlock_8 <|
  descRange_cons descBlock_9 <|
  descRange_cons descBlock_10 <|
  descRange_cons descBlock_11 <|
  descRange_cons descBlock_12 <|
  descRange_cons descBlock_13 <|
  descRange_cons descBlock_14 <|
  descRange_cons descBlock_15 <|
  descRange_cons descBlock_16 <|
  descRange_cons descBlock_17 <|
  descRange_cons descBlock_18 <|
  descRange_cons descBlock_19 <|
  descRange_cons descBlock_20 <|
  descRange_cons descBlock_21 <|
  descRange_cons descBlock_22 <|
  descRange_cons descBlock_23 <|
  descRange_cons descBlock_24 <|
  descRange_cons descBlock_25 <|
  descRange_cons descBlock_26 <|
  descRange_cons descBlock_27 <|
  descRange_cons descBlock_28 <|
  descRange_cons descBlock_29 <|
  descRange_cons descBlock_30 <|
  descRange_cons descBlock_31 <|
  descRange_nil _

/-- **Minimal orbit element bound.** If `m > 1` is the minimum of its own `T`-orbit, then
`2^17 ≤ m`. -/
theorem min_orbit_ge (m : ℕ) (hm1 : 1 < m) (hmin : ∀ j, m ≤ T^[j] m) : 2 ^ 17 ≤ m := by
  by_contra hc
  obtain ⟨j, hj⟩ := descRange_17 m (by omega) (by omega)
  exact absurd (hmin j) (by omega)

end CollatzSearch

#print axioms CollatzSearch.Tb_eq
#print axioms CollatzSearch.descends_sound
#print axioms CollatzSearch.checkBlock_sound
#print axioms CollatzSearch.descRange_cons
#print axioms CollatzSearch.descRange_17
#print axioms CollatzSearch.min_orbit_ge
