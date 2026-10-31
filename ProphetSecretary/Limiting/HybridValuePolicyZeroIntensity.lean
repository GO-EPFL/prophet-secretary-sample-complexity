import ProphetSecretary.Limiting.HybridValuePolicy

/-!
# Actual value-threshold optimality at zero anonymous intensity

The constructed zero-intensity law is the empty configuration. Every remaining
state is therefore the ordinary finite independent-instance problem, with all
retained identities still observed. The proved finite Bellman optimizer then
verifies the actual hybrid threshold policy at this boundary.
-/
open MeasureTheory Set
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma coe_remainingTime_eq_max (t : ℝ) : (remainingTime t : ℝ) = max 0 (1-t) := by
  rw [remainingTime,Real.coe_toNNReal',max_comm]

lemma FiniteIntensityHybridInstance.valueHybridThreshold_eq_finite_of_zero_intensity
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity = 0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (A : Finset (Fin n)) (t : ℝ) (i : Fin n) :
    B.valueHybridThreshold w c () A t (some i) = B.individuals.valueThreshold w c A t i := by
  let D := (B.restrictIndividuals (A.erase i)).remainingHorizon (remainingTime t)
  have hD : D.intensity = 0 := by simp [D,FiniteIntensityHybridInstance.remainingHorizon,
    FiniteIntensityHybridInstance.restrictIndividuals,hμ]
  have hV := D.value_zero_intensity ha hD hw (mul_nonneg hc (remainingTime t).property)
  change D.optimalScalarValue w (c*(remainingTime t : ℝ)) =
    Model.optimalScalarValue (B.individuals.restrictTo (A.erase i)) w (c*(remainingTime t : ℝ)) at hV
  change D.optimalScalarValue w (c*(remainingTime t : ℝ))/w = _
  rw [hV,coe_remainingTime_eq_max]
  rfl

lemma FiniteIntensityHybridInstance.emptyPoisson_valueThresholdPolicy_eq_finite
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity = 0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    emptyPoissonPolicy (B.valueThresholdPolicy hw hc) =
      B.individuals.valuePolicy (B.individuals.integrable_maximum_of_bounded B.individual_bounded) hw hc := by
  unfold emptyPoissonPolicy FiniteIntensityHybridInstance.valueThresholdPolicy Model.Instance.valuePolicy
  congr 1
  unfold FiniteIntensityHybridInstance.valueRule hybridThresholdRule Model.thresholdPolicy
  congr 1
  funext r t i x H
  change decide (B.valueHybridThreshold w c () (Model.unseen H) t (some i) ≤ x) =
    decide (B.individuals.valueThreshold w c (Model.unseen H) t i ≤ x)
  rw [B.valueHybridThreshold_eq_finite_of_zero_intensity ha hμ hw hc]

/-- This verifies the actual policy against the full hybrid policy supremum,
including μ=0, empty retained families and zero expected maximum. -/
theorem FiniteIntensityHybridInstance.valueThresholdPolicy_optimal_zero_intensity
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity = 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (B.valueThresholdPolicy hw.le hc).scalarObjective B w c = B.optimalScalarValue w c := by
  rw [emptyPoissonPolicy_scalarObjective _ B ha hμ w c,
    B.emptyPoisson_valueThresholdPolicy_eq_finite ha hμ hw.le hc,
    B.individuals.valuePolicy_optimal (B.individuals.integrable_maximum_of_bounded B.individual_bounded) hw hc,
    B.value_zero_intensity ha hμ hw.le hc]

end ProphetSecretary.Limiting
