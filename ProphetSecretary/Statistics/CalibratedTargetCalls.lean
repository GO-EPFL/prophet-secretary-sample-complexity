import ProphetSecretary.Statistics.CalibratedLearnerRandomness
import ProphetSecretary.Statistics.CalibrationQueryFailure
import ProphetSecretary.Statistics.CalibrationTargetBounds

/-!
# The actual target-query phase

The callback is evaluated at the public finite coefficient grid and receives
only the empirical first block and its own independent grid-indexed seed.
Ineligible data trigger the fixed target without evaluating the callback.
The numerical target statistics apply to these concrete returned tables.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m : ℕ} [NeZero m] {TSeed : Type*}

abbrev TargetEstimator (n m : ℕ) (TSeed : Type*) := Reservoir n m → ℝ → TSeed → ℝ

noncomputable def targetTable (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (a : (Fin n × Fin m) → ℝ) (r : TargetGrid m → TSeed) (j : TargetGrid m) : ℝ :=
  if targetEligible mu a then estimate (reservoirCoordinates.symm a) (targetGrid j) (r j) else 0

noncomputable def computedTarget (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (a : (Fin n × Fin m) → ℝ) (r : TargetGrid m → TSeed) : ℝ :=
  if targetEligible mu a then numericalTarget mu a (targetTable mu estimate a r) else 4/5

lemma computedTarget_eq_numericalTarget (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (a : (Fin n × Fin m) → ℝ) (r : TargetGrid m → TSeed) :
    computedTarget mu estimate a r=numericalTarget mu a (targetTable mu estimate a r) := by
  by_cases he : targetEligible mu a
  · simp only [computedTarget, if_pos he]
  · have hg : targetCountCutoff m < empiricalPositiveCount a ∨ trainingExpectedMaximum a < mu/2 := by
      by_contra h
      exact he ⟨le_of_not_gt (fun h' => h (Or.inl h')), le_of_not_gt (fun h' => h (Or.inr h'))⟩
    simp only [computedTarget, if_neg he, numericalTarget, if_pos hg]

lemma measurable_targetTable [MeasurableSpace TSeed] (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (hEstimate : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => estimate p.1 p.2.1 p.2.2)) :
    Measurable (fun p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → TSeed)) => targetTable mu estimate p.1 p.2) := by
  apply measurable_pi_lambda
  intro j
  have hGuard : MeasurableSet {p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → TSeed)) | targetEligible mu p.1} :=
    (measurableSet_le (measurable_empiricalPositiveCount.comp measurable_fst) measurable_const).inter
      (measurableSet_le measurable_const (measurable_trainingExpectedMaximum.comp measurable_fst))
  have hCall : Measurable (fun p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → TSeed)) =>
      estimate (reservoirCoordinates.symm p.1) (targetGrid j) (p.2 j)) :=
    hEstimate.comp ((reservoirCoordinates.symm.measurable.comp measurable_fst).prodMk
      ((measurable_const (a := targetGrid j)).prodMk ((measurable_pi_apply j).comp measurable_snd)))
  exact Measurable.ite hGuard hCall measurable_const

lemma measurable_computedTarget [MeasurableSpace TSeed] (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (hEstimate : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => estimate p.1 p.2.1 p.2.2)) :
    Measurable (fun p : (((Fin n × Fin m) → ℝ) × (TargetGrid m → TSeed)) => computedTarget mu estimate p.1 p.2) := by
  simp_rw [computedTarget_eq_numericalTarget]
  exact (measurable_numericalTarget mu).comp (measurable_fst.prodMk (measurable_targetTable mu estimate hEstimate))

lemma computedTarget_range (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (a : (Fin n × Fin m) → ℝ) (r : TargetGrid m → TSeed) :
    computedTarget mu estimate a r ∈ Icc (1/2 : ℝ) (4/5) := by
  rw [computedTarget_eq_numericalTarget]
  exact numericalTarget_range _ _ _

/-- The product seed array supplies the requested marginal law to each actual target call. -/
lemma targetTable_error_probability [MeasurableSpace TSeed] (νT : Measure TSeed) [IsProbabilityMeasure νT]
    (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (hEstimate : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => estimate p.1 p.2.1 p.2.2))
    (a : (Fin n × Fin m) → ℝ) (he : targetEligible mu a) (j : TargetGrid m) :
    (targetQueryArrayLaw νT).real {r | 1/(m : ℝ) <
      |targetTable mu estimate a r j-optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} =
      νT.real {r | 1/(m : ℝ) < |estimate (reservoirCoordinates.symm a) (targetGrid j) r-
        optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} := by
  let E : Set TSeed := {r | 1/(m : ℝ) < |estimate (reservoirCoordinates.symm a) (targetGrid j) r-
    optimalScalarValue (trainingInstance a) 1 (targetGrid j)|}
  have hCall : Measurable (fun r => estimate (reservoirCoordinates.symm a) (targetGrid j) r) :=
    hEstimate.comp (measurable_const.prodMk (measurable_const.prodMk measurable_id))
  have hE : MeasurableSet E := measurableSet_lt measurable_const (hCall.sub_const _).abs
  have hp := measurePreserving_eval (fun _ : TargetGrid m => νT) j
  simp only [targetTable, if_pos he]
  change (targetQueryArrayLaw νT).real ((fun r => r j) ⁻¹' E) = νT.real E
  rw [← map_measureReal_apply hp.measurable hE]
  exact congrArg (fun μ : Measure TSeed => μ.real E) hp.map_eq

lemma targetTable_conditional_confidence [MeasurableSpace TSeed] (P : Instance n) (νT : Measure TSeed) [IsProbabilityMeasure νT]
    (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (hEstimate : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => estimate p.1 p.2.1 p.2.2))
    (hConf : ∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
      νT.real {r | 1/(m : ℝ) < |estimate (reservoirCoordinates.symm a) (targetGrid j) r-
        optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} ≤ 1/((m : ℝ)^2*(4*(m : ℝ)+1))) :
    ∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
      (targetQueryArrayLaw νT).real {r | 1/(m : ℝ) < |targetTable mu estimate a r j-
        optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} ≤ 1/((m : ℝ)^2*(4*(m : ℝ)+1)) := by
  filter_upwards [hConf] with a ha he j
  rw [targetTable_error_probability νT mu estimate hEstimate a he j]
  exact ha he j

end ProphetSecretary.Statistics.Calibration
