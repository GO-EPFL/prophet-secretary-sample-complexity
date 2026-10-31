import ProphetSecretary.Model.BoundaryDecomposition

/-!
# Conditional pending-candidate regret

This integrates the candidate's independent uniform clock while fixing every
other coordinate. The pending survival event belongs to the old policy, and
its domination is uniform over the complete residual data.
-/

open MeasureTheory Set Filter
open scoped Classical Topology BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.conditionalDurationRegret (P : Instance n) (π : Policy Unit n)
    (z z' : ℝ) (x u : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∫ t : ℝ, if t ≤ π.pendingTime () x u i then P.durationActionLoss z z' i (x i) u t else 0
    ∂Instance.uniformClock

lemma Instance.integrable_pendingDurationLoss (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Unit n)
    {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z') (x u : Fin n → ℝ) (i : Fin n) :
    Integrable (fun t : ℝ ↦ if t ≤ π.pendingTime () x u i then
      P.durationActionLoss z z' i (x i) u t else 0) Instance.uniformClock := by
  have h := (P.integrable_durationActionLoss hP hz hz' i (x i) u).indicator
    (s := Iic (π.pendingTime () x u i)) measurableSet_Iic
  exact h.congr (Filter.Eventually.of_forall (fun t ↦ by simp only [Set.indicator, mem_Iic]))

lemma Instance.conditionalDurationRegret_eq_volume (P : Instance n) (π : Policy Unit n)
    (z z' : ℝ) (x u : Fin n → ℝ) (i : Fin n) :
    P.conditionalDurationRegret π z z' x u i =
      ∫ t : ℝ, if t ∈ Icc (0 : ℝ) 1 ∧ t ≤ π.pendingTime () x u i then
        P.durationActionLoss z z' i (x i) u t else 0 := by
  unfold Instance.conditionalDurationRegret Instance.uniformClock
  rw [← integral_indicator measurableSet_Icc]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun t ↦ by
    by_cases ht : t ∈ Icc (0 : ℝ) 1 <;> simp [Set.indicator, ht])

lemma Instance.conditionalDurationRegret_nonnegative (P : Instance n) (π : Policy Unit n)
    (z z' : ℝ) (x u : Fin n → ℝ) (i : Fin n) : 0 ≤ P.conditionalDurationRegret π z z' x u i := by
  apply integral_nonneg
  intro t
  dsimp only
  split_ifs
  · exact P.durationActionLoss_nonnegative _ _ _ _ _ _
  · exact le_rfl

lemma Instance.conditionalDurationRegret_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Unit n)
    {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 < z') (x u : Fin n → ℝ) (i : Fin n) :
    P.conditionalDurationRegret π z z' x u i ≤ 8 * (1 + (n : ℝ)) * (z - z') ^ 2 / z' := by
  apply le_trans (integral_mono (P.integrable_pendingDurationLoss hP π hz hz'.le x u i)
    (P.integrable_durationActionLoss hP hz hz'.le i (x i) u) ?_)
    (P.integral_durationActionLoss_le hP hz hz' i (x i) u)
  intro t
  dsimp only
  split_ifs
  · exact le_rfl
  · exact P.durationActionLoss_nonnegative _ _ _ _ _ _

lemma Instance.eventually_integrable_stateBranch (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (π : Policy Unit n)
    (x u : Fin n → ℝ) (i : Fin n) (A : Finset (Fin n)) {z : ℝ} (hz : 0 < z)
    (hr0 : (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (x i) ≠ 0)
    (hru : ∀ j, j ≠ i →
      (P.restrictTo A).crossingTime (P.restrictTo_integrable_maximum A hP) z (x i) ≠ u j) :
    ∀ᶠ h : ℝ in 𝓝 0, Integrable (fun t : ℝ ↦ π.branchMultiplier () x u i A t *
      P.stateBranchLoss hP A z (z + h) (x i) t) volume := by
  by_cases hx : optimalScalarValue (P.restrictTo A) 1 0 < x i
  · let Q := P.restrictTo A
    have hQ := P.restrictTo_integrable_maximum A hP
    have hd := Q.durationRoot_positive hQ hx
    have hr1 : Q.crossingTime hQ z (x i) ≠ 1 := by
      unfold Instance.crossingTime
      have hp := div_pos hd hz
      linarith
    have hm := π.branchMultiplier_eventually_eq () x u i A hr0 hr1 hru
    filter_upwards [ProphetSecretary.Analysis.eventually_weighted_branch_integral
      (Q.saturatedDurationValue_continuous hQ) (Q.saturatedDurationValue_level_iff hQ hd) hz hm] with h hh
    simpa only [Instance.stateBranchLoss, if_pos hx] using hh.1
  · exact Filter.Eventually.of_forall (fun h ↦ by
      simp only [Instance.stateBranchLoss, if_neg hx, mul_zero]
      exact integrable_zero ℝ ℝ volume)

end ProphetSecretary.Model
