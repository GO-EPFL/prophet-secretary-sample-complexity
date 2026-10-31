import ProphetSecretary.Limiting.ContinuousWeightedExtraction
import Mathlib.MeasureTheory.Measure.SubFinite

/-!
# Constructing the positive weighted residual after all retained individuals

The exact prefix identities supplied by actual extraction dominate every
finite sum of retained weighted marginal measures. Taking the genuine
countable measure sum preserves that domination, so subtraction constructs a
positive finite residual and yields an exact measure decomposition.
Weighted mass at or below the terminal reserve is retained analytically
here and erased when forming the intensity strictly above that reserve.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Limiting

noncomputable def retainedContinuousWeightedMeasure (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ) : Measure ℝ :=
  Measure.sum fun i => (continuousWeightedLaw (Q i) w : Measure ℝ)

/-- Positivity of the eventual residual follows from the actually proved
finite-prefix subtraction identities, rather than a positivity interface. -/
theorem retainedContinuousWeightedMeasure_le_initial (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) :
    retainedContinuousWeightedMeasure w Q ≤ (ρ 0 : Measure ℝ) := by
  apply Measure.le_iff.mpr
  intro s hs
  rw [retainedContinuousWeightedMeasure,Measure.sum_apply _ hs,ENNReal.tsum_eq_iSup_nat]
  apply iSup_le
  intro N
  have hp := continuousWeighted_residual_prefix_identity w Q ρ hρ N
  have heval := congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ) s) hp
  rw [FiniteMeasure.toMeasure_add,Measure.add_apply,FiniteMeasure.toMeasure_sum,Measure.finsetSum_apply] at heval
  rw [heval]
  exact le_add_of_nonneg_right (show (0 : ENNReal) ≤ (ρ N : Measure ℝ) s from bot_le)

noncomputable def extractedContinuousWeightedResidual (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) : FiniteMeasure ℝ :=
  ⟨(ρ 0 : Measure ℝ) - retainedContinuousWeightedMeasure w Q,
    isFiniteMeasure_of_le (ρ 0 : Measure ℝ) Measure.sub_le⟩

/-- The countable retained part is genuinely finite under the extracted prefix
bounds. It may contain infinitely many nonzero individuals. -/
theorem retainedContinuousWeightedMeasure_isFinite (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) :
    IsFiniteMeasure (retainedContinuousWeightedMeasure w Q) :=
  isFiniteMeasure_of_le (ρ 0 : Measure ℝ) (retainedContinuousWeightedMeasure_le_initial w Q ρ hρ)

/-- Exact positive-measure decomposition after every individual is retained. -/
theorem extractedContinuousWeightedResidual_add_retained (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ)
    (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) :
    (extractedContinuousWeightedResidual w Q ρ : Measure ℝ) + retainedContinuousWeightedMeasure w Q = (ρ 0 : Measure ℝ) := by
  letI := retainedContinuousWeightedMeasure_isFinite w Q ρ hρ
  exact Measure.sub_add_cancel_of_le (retainedContinuousWeightedMeasure_le_initial w Q ρ hρ)

lemma extractedContinuousWeightedResidual_le_initial (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) :
    (extractedContinuousWeightedResidual w Q ρ : Measure ℝ) ≤ (ρ 0 : Measure ℝ) := Measure.sub_le

lemma extractedContinuousWeightedResidual_supported_interval (w : ℝ →ᵇ ℝ)
    (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ) {H : ℝ}
    (hcap : (ρ 0 : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) :
    (extractedContinuousWeightedResidual w Q ρ : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 := by
  have h := Measure.le_iff.mp (extractedContinuousWeightedResidual_le_initial w Q ρ) ((Icc (0 : ℝ) H)ᶜ) measurableSet_Icc.compl
  rw [hcap] at h
  exact le_antisymm h bot_le

end ProphetSecretary.Limiting
