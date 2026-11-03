import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Max
import Mathlib.Tactic.Linarith

/-!
# Ordered numerical continuation thresholds

The cumulative maximum in `eq:calibration-thresholds` makes approximate
thresholds monotone in the coefficient. Accurate estimates retain the same
absolute error after this operation and the duration floor.
-/

namespace ProphetSecretary.Statistics

private lemma continuationPrefix_nonempty (j : ℕ) : (Finset.range (j + 1)).Nonempty :=
  ⟨0, Finset.mem_range.mpr (Nat.zero_lt_succ j)⟩

/-- The implemented continuation threshold at coefficient index `j`. -/
noncomputable def nestedContinuation (z estimate : ℕ → ℝ) (u : ℝ) (j : ℕ) : ℝ :=
  max (z j * u) ((Finset.range (j + 1)).sup' (continuationPrefix_nonempty j) estimate)

lemma durationFloor_le_nestedContinuation (z estimate : ℕ → ℝ) (u : ℝ) (j : ℕ) :
    z j * u ≤ nestedContinuation z estimate u j := le_max_left _ _

lemma estimate_le_nestedContinuation (z estimate : ℕ → ℝ) (u : ℝ) (j : ℕ) :
    estimate j ≤ nestedContinuation z estimate u j :=
  (Finset.le_sup' estimate (Finset.mem_range.mpr (Nat.lt_succ_self j))).trans
    (le_max_right _ _)

lemma nestedContinuation_monotone (z estimate : ℕ → ℝ) {u : ℝ}
    (hu : 0 ≤ u) (hz : Monotone z) : Monotone (nestedContinuation z estimate u) := by
  intro i j hij
  apply max_le
  · exact (mul_le_mul_of_nonneg_right (hz hij) hu).trans
      (durationFloor_le_nestedContinuation z estimate u j)
  · apply Finset.sup'_le
    intro l hl
    exact (Finset.le_sup' estimate (Finset.mem_range.mpr
      ((Finset.mem_range.mp hl).trans_le (Nat.add_le_add_right hij 1)))).trans
      (le_max_right _ _)

/-- The cumulative maximum does not enlarge a uniform estimation error. -/
theorem nestedContinuation_error (z estimate value : ℕ → ℝ) (u : ℝ) (j : ℕ)
    {h : ℝ} (hh : 0 ≤ h) (hmono : Monotone value)
    (hfloor : z j * u ≤ value j)
    (haccurate : ∀ l ≤ j, |estimate l - value l| ≤ h) :
    |nestedContinuation z estimate u j - value j| ≤ h := by
  have hlower := (abs_le.mp (haccurate j le_rfl)).1
  have hupper : nestedContinuation z estimate u j ≤ value j + h := by
    apply max_le
    · linarith
    · apply Finset.sup'_le
      intro l hl
      have hlj : l ≤ j := Nat.le_of_lt_succ (Finset.mem_range.mp hl)
      have he := (abs_le.mp (haccurate l hlj)).2
      have hm := hmono hlj
      linarith
  exact abs_le.mpr ⟨by linarith [estimate_le_nestedContinuation z estimate u j],
    by linarith⟩

end ProphetSecretary.Statistics
