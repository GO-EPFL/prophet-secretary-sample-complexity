import ProphetSecretary.Statistics.CalibratedOfflineLaw
import ProphetSecretary.Statistics.CalibratedRightExtension
import ProphetSecretary.Statistics.CalibrationTargetBounds

/-!
# Statistics of the actual offline preparation

The target depends only on the first block and target seeds. The signed
error depends on the full selected interpolation point. The independent
validation law gives the right-extension probability and transports the
calibration moments to the same offline experiment.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

section
variable (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (mu : ℝ) {zlo zhi : ℝ}
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "D" => OfflineData n m J TSeed PSeed
local notation "O" => offlineDataLaw (m := m) (J := J) P νT νP
local notation "g" => offlineCalibrationError (J := J) P νP mu zlo zhi targetEstimate policyEstimate

omit [NeZero m] in
lemma offline_firstCoordinate_measurePreserving :
    MeasurePreserving (fun d : D => d.1.1) O (P.trainingCoordinateLaw m) :=
  measurePreserving_fst.comp measurePreserving_fst

omit [NeZero m] in
lemma offlineEmpiricalBlock_measurePreserving :
    MeasurePreserving (offlineEmpiricalBlock : D → Reservoir n m) O (P.reservoirLaw m) :=
  (P.reservoirCoordinates_symm_measurePreserving m).comp
    (offline_firstCoordinate_measurePreserving P νT νP)

omit [NeZero m] in
lemma offlineEmpiricalBlock_unit_ae (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) :
    ∀ᵐ d : D ∂O, ∀ i j, offlineEmpiricalBlock d i j∈Icc (0 : ℝ) 1 := by
  have hp := offline_firstCoordinate_measurePreserving (m := m) (J := J) P νT νP
  have hn : ∀ᵐ a ∂P.trainingCoordinateLaw m, ∀ i j, 0≤reservoirCoordinates.symm a i j := by
    simp only [ae_all_iff]
    intro i j
    exact (measurePreserving_eval (fun a : Fin n × Fin m => P.law a.1) (i,j)).quasiMeasurePreserving.ae
      (P.nonnegative i)
  filter_upwards [hp.quasiMeasurePreserving.ae (trainingCoordinates_unit_ae P hcap),
    hp.quasiMeasurePreserving.ae hn] with d hd h0 i j
  exact ⟨h0 i j,hd i j⟩

include hT hC in
lemma measurable_offlineCalibrationError : Measurable g :=
  measurable_validationSelectionError P νP zlo zhi policyEstimate hC
    measurable_offlineEmpiricalBlock measurable_snd (measurable_offlineTarget mu targetEstimate hT)

omit [MeasurableSpace TSeed] in
include hC in
lemma offlineCalibrationError_abs_le_one (hz : zlo≤zhi) (d : D) : |g d|≤1 := by
  have hr := computedTarget_range mu targetEstimate d.1.1 d.1.2
  have hρ : computedTarget mu targetEstimate d.1.1 d.1.2 ∈ Icc (0 : ℝ) 1 :=
    ⟨(by norm_num : (0 : ℝ)≤1/2).trans hr.1,hr.2.trans (by norm_num)⟩
  exact validationSelectionError_abs_le_one P νP hz policyEstimate hC (offlineEmpiricalBlock d) hρ d.2

include hT hC in
theorem offlineCalibrationError_moments (hz : zlo≤zhi) :
    |∫ d, g d ∂O| ≤1/((m : ℝ)+1) ∧ (∫ d,(g d)^2 ∂O)≤4/(m : ℝ) := by
  have hm := measurable_offlineCalibrationError (J := J) P νP mu targetEstimate policyEstimate hT hC
    (zlo := zlo) (zhi := zhi)
  have hMap := calibratedOfflineData_measurePreserving (m := m) (J := J) P νT νP
  have h1 := hMap.hasLaw.integral_comp hm.aestronglyMeasurable
  have h2 := hMap.hasLaw.integral_comp (hm.pow_const 2).aestronglyMeasurable
  have h := actualCalibrationError_moments (J := J) P νT νP mu hz targetEstimate policyEstimate hT hC
  change |∫ x,(g ∘ calibratedOfflineData) x ∂(P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP)|≤1/((m : ℝ)+1) ∧
    (∫ x,((fun d => (g d)^2) ∘ calibratedOfflineData) x
      ∂(P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP))≤4/(m : ℝ) at h
  rwa [h1,h2] at h

omit [IsProbabilityMeasure νT] in
include hT in
lemma offlineTarget_integral (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ d : D, f (offlineTarget mu targetEstimate d) ∂O)=
      ∫ p : FirstInformation n m TSeed, f (numericalTarget mu p.1 (targetTable mu targetEstimate p.1 p.2))
        ∂firstInformationLaw P νT := by
  have ht := measurable_computedTarget mu targetEstimate hT
  have hMap := (measurePreserving_fst (μ := firstInformationLaw (m := m) P νT)
    (ν := validationWorldArrayLaw (m := m) (J := J) P νP)).hasLaw.integral_comp
    (hf.comp ht).aestronglyMeasurable
  calc
    _ = ∫ p : FirstInformation n m TSeed, f (computedTarget mu targetEstimate p.1 p.2) ∂firstInformationLaw P νT :=
      hMap
    _ = _ := by simp only [computedTarget_eq_numericalTarget]

include hT hC in
theorem offline_right_probability_le (hP : Integrable Instance.maximum P.valuesLaw)
    (hM : P.expectedMaximum≤1/80) (h0 : 0≤zlo) (hz : zlo≤1/4) (hJ : 0<J) :
    (O).real {d : D | (offlinePrepare mu zlo (1/4) targetEstimate policyEstimate d).2.1=J+2} ≤
      Real.exp (-9*(m : ℝ)/200) := by
  let A := {d : D | (offlinePrepare mu zlo (1/4) targetEstimate policyEstimate d).2.1=J+2}
  let F := A.indicator (fun _ : D => (1 : ℝ))
  have hA : MeasurableSet A := measurableSet_eq_fun
    (measurable_fst.comp (measurable_snd.comp
      (measurable_offlinePrepare mu zlo (1/4) targetEstimate policyEstimate hT hC))) measurable_const
  have hI : Integrable F O := (integrable_const (1 : ℝ)).indicator hA
  let I := firstInformationLaw (m := m) P νT
  let W := validationWorldArrayLaw (m := m) (J := J) P νP
  have hF (p : FirstInformation n m TSeed) :
      (∫ w, F (p,w) ∂W)≤Real.exp (-9*(m : ℝ)/200) := by
    let Fst (w : ValidationWorldArray n m J PSeed) : D := (p,w)
    let B := Fst ⁻¹' A
    have hB : MeasurableSet B := hA.preimage (show Measurable Fst from measurable_const.prodMk measurable_id)
    have hEq : (fun w => F (p,w))=B.indicator (fun _ => (1 : ℝ)) := rfl
    rw [hEq]
    change (∫ w,B.indicator (1 : ValidationWorldArray n m J PSeed → ℝ) w ∂W)≤_
    rw [integral_indicator_one hB]
    have hR := computedTarget_range mu targetEstimate p.1 p.2
    have hRight := validationSelection_right_probability_le P νP hP hM h0 hz hJ policyEstimate hC
      (reservoirCoordinates.symm p.1) ⟨(by norm_num : (0 : ℝ)<1/2).trans_le hR.1,hR.2⟩
    simpa only [B,Fst,A,Set.preimage_setOf_eq,offlinePrepare,offlineEmpiricalBlock,offlineTarget] using hRight
  change (I.prod W).real A≤_
  rw [← integral_indicator_one hA]
  change (∫ d,F d ∂I.prod W)≤_
  rw [integral_prod _ (show Integrable F (I.prod W) from hI)]
  have h := integral_mono (show Integrable (fun p => ∫ w,F (p,w) ∂W) I from hI.integral_prod_left)
    (integrable_const (Real.exp (-9*(m : ℝ)/200))) hF
  simpa only [integral_const,probReal_univ,one_smul] using h

end

end ProphetSecretary.Statistics.Calibration
