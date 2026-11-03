import ProphetSecretary.Statistics.CalibratedLearner
import Mathlib.Probability.HasLaw

/-!
# Calibration moments under the actual learner's training law

The two-block regrouping exposes the first-block information and iid
validation profiles as a product. Integrating the fixed-information moments
there and transporting back gives bounds for the actual prepared selector.
The independent online seed and coin do not enter this analytical error.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed]

abbrev FirstInformation (n m : ℕ) (TSeed : Type*) :=
  ((Fin n × Fin m) → ℝ) × (TargetGrid m → TSeed)
abbrev ValidationWorldArray (n m J : ℕ) (PSeed : Type*) := Fin m → World n (PolicyQueryArray n J PSeed)

noncomputable def firstInformationLaw (P : Instance n) (νT : Measure TSeed) : Measure (FirstInformation n m TSeed) :=
  (P.trainingCoordinateLaw m).prod (targetQueryArrayLaw νT)

instance firstInformationLaw_probability (P : Instance n) (νT : Measure TSeed) [IsProbabilityMeasure νT] :
    IsProbabilityMeasure (firstInformationLaw (m := m) P νT) := by unfold firstInformationLaw; infer_instance

noncomputable def validationWorldArrayLaw (P : Instance n) (νP : Measure PSeed) :
    Measure (ValidationWorldArray n m J PSeed) :=
  Measure.pi (fun _ => P.worldLaw (policyQueryArrayLaw νP))

instance validationWorldArrayLaw_probability (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (validationWorldArrayLaw (m := m) (J := J) P νP) := by
  unfold validationWorldArrayLaw
  infer_instance

def calibratedOfflineData (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) :
    FirstInformation n m TSeed × ValidationWorldArray n m J PSeed :=
  let d := calibratedExperiment p
  (d.1,d.2.1)

lemma calibratedOfflineData_measurePreserving (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    MeasurePreserving (calibratedOfflineData (n := n) (m := m) (J := J))
      ((P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP))
      ((firstInformationLaw P νT).prod (validationWorldArrayLaw P νP)) := by
  exact ((MeasurePreserving.id (firstInformationLaw (m := m) P νT)).prod measurePreserving_fst).comp
    (calibratedExperiment_measurePreserving (m := m) (J := J) P νT νP)

noncomputable def offlineCalibrationError [NeZero m]
    (P : Instance n) (νP : Measure PSeed) (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : FirstInformation n m TSeed × ValidationWorldArray n m J PSeed) : ℝ :=
  validationSelectionError P νP zlo zhi policyEstimate (reservoirCoordinates.symm d.1.1)
    (computedTarget mu targetEstimate d.1.1 d.1.2) d.2

/-- The full-point calibration error of the actual raw training outcome. -/
noncomputable def actualCalibrationError [NeZero m]
    (P : Instance n) (νP : Measure PSeed) (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) : ℝ :=
  offlineCalibrationError P νP mu zlo zhi targetEstimate policyEstimate (calibratedOfflineData p)

/-- Bias and second moment for the actual transcript-based calibrated learner. -/
theorem actualCalibrationError_moments [NeZero m]
    (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (mu : ℝ) {zlo zhi : ℝ} (hz : zlo ≤ zhi)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    |∫ p, actualCalibrationError (J := J) P νP mu zlo zhi targetEstimate policyEstimate p
      ∂(P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP)| ≤ 1/((m : ℝ)+1) ∧
    (∫ p, (actualCalibrationError (J := J) P νP mu zlo zhi targetEstimate policyEstimate p)^2
      ∂(P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP)) ≤ 4/(m : ℝ) := by
  let I := firstInformationLaw (m := m) P νT
  let W := validationWorldArrayLaw (m := m) (J := J) P νP
  let G := offlineCalibrationError (J := J) P νP mu zlo zhi targetEstimate policyEstimate
  have hG : Measurable G := measurable_validationSelectionError P νP zlo zhi policyEstimate hC
    (reservoirCoordinates.symm.measurable.comp (measurable_fst.comp measurable_fst)) measurable_snd
    ((measurable_computedTarget mu targetEstimate hT).comp measurable_fst)
  have hBound (d : FirstInformation n m TSeed × ValidationWorldArray n m J PSeed) : |G d|≤1 := by
    have hr := computedTarget_range mu targetEstimate d.1.1 d.1.2
    have hρ : computedTarget mu targetEstimate d.1.1 d.1.2 ∈ Icc (0 : ℝ) 1 :=
      ⟨by linarith [hr.1],by linarith [hr.2]⟩
    exact validationSelectionError_abs_le_one P νP hz policyEstimate hC (reservoirCoordinates.symm d.1.1) hρ d.2
  have hGI : Integrable G (I.prod W) := Integrable.of_bound hG.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun d => by simpa only [Real.norm_eq_abs] using hBound d)
  have hG2I : Integrable (fun d => G d^2) (I.prod W) := by
    apply Integrable.of_bound (hG.pow_const 2).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun d => by
      rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
      have h := pow_le_pow_left₀ (abs_nonneg (G d)) (hBound d) 2
      simpa only [sq_abs,one_pow] using h
  have hMom (d : FirstInformation n m TSeed) :
      |∫ w, G (d,w) ∂W|≤1/((m : ℝ)+1) ∧ (∫ w, G (d,w)^2 ∂W)≤4/(m : ℝ) := by
    have hr := computedTarget_range mu targetEstimate d.1 d.2
    have hρ : computedTarget mu targetEstimate d.1 d.2 ∈ Ioc (0 : ℝ) 1 :=
      ⟨by linarith [hr.1],by linarith [hr.2]⟩
    simpa only [G,W,offlineCalibrationError,validationWorldArrayLaw] using
      validationSelection_error_moments (m := m) (J := J) P νP hz policyEstimate hC
        (reservoirCoordinates.symm d.1) hρ
  have hMap := calibratedOfflineData_measurePreserving (m := m) (J := J) P νT νP
  have he := hMap.hasLaw.integral_comp hGI.aestronglyMeasurable
  have he2 := hMap.hasLaw.integral_comp hG2I.aestronglyMeasurable
  simp only [Function.comp_def] at he he2
  unfold actualCalibrationError
  change |∫ p, G (calibratedOfflineData p) ∂(P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP)| ≤ 1/((m : ℝ)+1) ∧
    (∫ p, G (calibratedOfflineData p)^2 ∂(P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP)) ≤ 4/(m : ℝ)
  constructor
  · rw [he,integral_prod _ hGI]
    apply abs_integral_le_integral_abs.trans
    have h := integral_mono hGI.integral_prod_left.abs (integrable_const (1/((m : ℝ)+1))) (fun d => (hMom d).1)
    simpa only [integral_const,probReal_univ,one_smul] using h
  · rw [he2,integral_prod _ hG2I]
    have h := integral_mono hG2I.integral_prod_left (integrable_const (4/(m : ℝ))) (fun d => (hMom d).2)
    simpa only [integral_const,probReal_univ,one_smul] using h

end ProphetSecretary.Statistics.Calibration
