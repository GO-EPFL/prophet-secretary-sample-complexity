import ProphetSecretary.Limiting.BoundedMomentDataExtraction
import Mathlib.MeasureTheory.Measure.SubFinite

/-!
# Constructing the positive weighted residual after all retained individuals

The exact prefix identities supplied by actual extraction dominate every
finite sum of retained weighted marginal measures. Taking the genuine
countable measure sum preserves that domination, so subtraction constructs a
positive finite residual and yields an exact measure decomposition.
Any atom of the weighted residual at zero is retained analytically here; it
must be erased when forming the unweighted positive-mark intensity.
-/
open MeasureTheory Set
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Limiting

noncomputable def retainedWeightedMeasure (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ) : Measure ℝ :=
  Measure.sum fun i => (valueWeightedLaw (Q i) H : Measure ℝ)

/-- Positivity of the eventual residual follows from the actually proved
finite-prefix subtraction identities, rather than a positivity interface. -/
theorem retainedWeightedMeasure_le_initial (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1)) :
    retainedWeightedMeasure H Q ≤ (ρ 0 : Measure ℝ) := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [retainedWeightedMeasure,Measure.sum_apply _ hs,ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  have hp := extracted_residual_prefix_identity H Q ρ hρ N
  have heval := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) s) hp
  rw [FiniteMeasure.toMeasure_add,Measure.add_apply,FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply] at heval
  rw [heval]
  exact le_add_of_nonneg_right (show (0 : ENNReal) ≤ (ρ N : Measure ℝ) s from bot_le)

noncomputable def extractedWeightedResidual (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) : FiniteMeasure ℝ :=
  ⟨(ρ 0 : Measure ℝ) - retainedWeightedMeasure H Q,
    isFiniteMeasure_of_le (ρ 0 : Measure ℝ) Measure.sub_le⟩

/-- The countable retained part is genuinely finite under the extracted prefix
bounds. It may contain infinitely many nonzero individuals. -/
theorem retainedWeightedMeasure_isFinite (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1)) :
    IsFiniteMeasure (retainedWeightedMeasure H Q) :=
  isFiniteMeasure_of_le (ρ 0 : Measure ℝ) (retainedWeightedMeasure_le_initial H Q ρ hρ)

/-- Exact positive-measure decomposition after every individual is retained. -/
theorem extractedWeightedResidual_add_retained (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1)) :
    (extractedWeightedResidual H Q ρ : Measure ℝ) + retainedWeightedMeasure H Q = (ρ 0 : Measure ℝ) := by
  letI := retainedWeightedMeasure_isFinite H Q ρ hρ
  exact Measure.sub_add_cancel_of_le (retainedWeightedMeasure_le_initial H Q ρ hρ)

lemma extractedWeightedResidual_le_initial (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) :
    (extractedWeightedResidual H Q ρ : Measure ℝ) ≤ (ρ 0 : Measure ℝ) := Measure.sub_le

lemma extractedWeightedResidual_supported_interval (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hcap : (ρ 0 : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    (extractedWeightedResidual H Q ρ : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
  have h := Measure.le_iff.mp (extractedWeightedResidual_le_initial H Q ρ) ((Icc (0 : ℝ) (H : ℝ))ᶜ) measurableSet_Icc.compl
  rw [hcap] at h
  exact le_antisymm h bot_le

end ProphetSecretary.Limiting
