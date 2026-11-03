import ProphetSecretary.Statistics.CalibratedOfflineLaw
import ProphetSecretary.Statistics.EmpiricalCapRegret
import ProphetSecretary.Statistics.CalibrationCountCutoff

/-!
# Regret of the exact empirical comparison policies

The endpoint coefficient may be selected by any measurable function of
the offline data. Regrouping the actual training law makes the first
empirical block independent of the remaining auxiliary variables, so the
data-selected empirical regret bound applies.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [NeZero m]

noncomputable def exactCalibrationEndpoint (q : Reservoir n m) (z : ℝ) : RandomizedPolicy n :=
  (Learner.empiricalCapAcceptance Unit (Measure.dirac ()) (fun _ => z) measurable_const).frozenRandomizedPolicy q ()

lemma exactCalibrationEndpoint_decide (q : Reservoir n m) (z : ℝ) (s : Unit) (t : ℝ)
    (i : Fin n) (x : ℝ) (H : History n) :
    (exactCalibrationEndpoint q z).rule.decide s t i x H=
      decide (0<x ∧ empiricalCapThreshold q z (unseen H) t i≤x) :=
  Learner.empiricalCapAcceptance_decide Unit (Measure.dirac ()) (fun _ => z) measurable_const q () t i x H

variable [MeasurableSpace TSeed] [MeasurableSpace PSeed]

abbrev ExactComparisonAux (n m J : ℕ) (TSeed PSeed : Type) :=
  (TargetGrid m → TSeed) × ValidationWorldArray n m J PSeed

noncomputable def exactComparisonAuxLaw (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed) :
    Measure (ExactComparisonAux n m J TSeed PSeed) :=
  (targetQueryArrayLaw νT).prod (validationWorldArrayLaw P νP)

instance exactComparisonAuxLaw_probability (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (exactComparisonAuxLaw (m := m) (J := J) P νT νP) := by
  unfold exactComparisonAuxLaw
  infer_instance

def exactComparisonDataEquiv :
    OfflineData n m J TSeed PSeed ≃ᵐ Reservoir n m × ExactComparisonAux n m J TSeed PSeed :=
  MeasurableEquiv.prodAssoc.trans (reservoirCoordinates.symm.prodCongr (MeasurableEquiv.refl _))

omit [NeZero m] in
lemma exactComparisonData_measurePreserving (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    MeasurePreserving (exactComparisonDataEquiv (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed))
      (offlineDataLaw P νT νP) ((P.reservoirLaw m).prod (exactComparisonAuxLaw P νT νP)) := by
  exact ((P.reservoirCoordinates_symm_measurePreserving m).prod
    (MeasurePreserving.id (exactComparisonAuxLaw (m := m) (J := J) P νT νP))).comp
      (measurePreserving_prodAssoc (P.trainingCoordinateLaw m) (targetQueryArrayLaw νT)
        (validationWorldArrayLaw P νP))

omit [NeZero m] in
lemma exactComparisonData_fst (d : OfflineData n m J TSeed PSeed) :
    (exactComparisonDataEquiv d).1=offlineEmpiricalBlock d := rfl

/-- The exact endpoint has the old data-selected regret bound under the new actual training law. -/
theorem exactCalibrationEndpoint_selected_regret_le (P : Instance n)
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80)
    {lo : ℝ} (hlo : 0<lo) (hlohi : lo≤1/4)
    (Z : OfflineData n m J TSeed PSeed → ℝ) (hZ : Measurable Z)
    (hRange : ∀ d, Z d∈Icc lo (1/4 : ℝ)) :
    let r := fun d => optimalScalarValue P 1 (Z d)-
      (exactCalibrationEndpoint (offlineEmpiricalBlock d) (Z d)).scalarObjective P 1 (Z d)
    Integrable r (offlineDataLaw P νT νP) ∧
      (∫ d,r d ∂offlineDataLaw P νT νP)≤empiricalCapRegretConstant lo*
        (1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ) := by
  let D := OfflineData n m J TSeed PSeed
  let S := ExactComparisonAux n m J TSeed PSeed
  let η := exactComparisonAuxLaw (m := m) (J := J) P νT νP
  let E := exactComparisonDataEquiv (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed)
  let T := Z ∘ E.symm
  have hT : Measurable T := hZ.comp E.symm.measurable
  have hTRange (p : Reservoir n m × S) : T p∈Icc lo (1/4 : ℝ) := hRange _
  let L := Learner.empiricalCapAcceptance S η T hT
  have hP := P.integrable_maximum_of_bounded hcap
  let f := fun p : Reservoir n m × S => optimalScalarValue P 1 (T p)-
    (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (T p)
  have hf := L.integrable_selectedRegret P hP hT
    (fun p => hlo.le.trans (hTRange p).1) (Filter.Eventually.of_forall fun p => (hTRange p).2)
  have hRate := Learner.empiricalCapAcceptance_expected_regret_le S η T hT hlo hlohi hTRange P hcap hM
  have hMap := exactComparisonData_measurePreserving (m := m) (J := J) P νT νP
  have hF (d : D) : f (E d)=optimalScalarValue P 1 (Z d)-
      (exactCalibrationEndpoint (offlineEmpiricalBlock d) (Z d)).scalarObjective P 1 (Z d) := by
    have hZEq : T (E d)=Z d := congrArg Z (E.symm_apply_apply d)
    have hQ : (E d).1=offlineEmpiricalBlock d := rfl
    have hDec : (L.frozenRule (E d).1 (E d).2).decide=
        (exactCalibrationEndpoint (offlineEmpiricalBlock d) (Z d)).rule.decide := by
      funext s t i x H
      have hL : L.policy.decide (E d) t i x H =
          decide (0<x ∧ empiricalCapThreshold (E d).1 (T (E d)) (unseen H) t i≤x) :=
        Learner.empiricalCapAcceptance_decide S η T hT (E d).1 (E d).2 t i x H
      have hR := exactCalibrationEndpoint_decide (offlineEmpiricalBlock d) (Z d) s t i x H
      rw [hQ,hZEq] at hL
      exact hL.trans hR.symm
    have hRule : L.frozenRule (E d).1 (E d).2 =
        (exactCalibrationEndpoint (offlineEmpiricalBlock d) (Z d)).rule := congrArg Policy.mk hDec
    change optimalScalarValue P 1 (T (E d))-(L.frozenRandomizedPolicy (E d).1 (E d).2).scalarObjective P 1 (T (E d))=_
    rw [hZEq]
    congr 1
    change (∫ ω : World n Unit, 1*(L.frozenRule (E d).1 (E d).2).reward ω.2.2 Finset.univ ω.1 ω.2.1+
        Z d*(L.frozenRule (E d).1 (E d).2).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()))=_
    exact congrArg (fun p : Policy Unit n => ∫ ω : World n Unit,
      1*p.reward ω.2.2 Finset.univ ω.1 ω.2.1+
        Z d*p.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ())) hRule
  refine ⟨(hMap.integrable_comp_of_integrable hf).congr (Filter.Eventually.of_forall hF),?_⟩
  have hMean := hMap.hasLaw.integral_comp hf.aestronglyMeasurable
  calc
    _ = ∫ d,(f ∘ E) d ∂offlineDataLaw P νT νP :=
      integral_congr_ae (Filter.Eventually.of_forall fun d => (hF d).symm)
    _ = ∫ p,f p ∂(P.reservoirLaw m).prod η := hMean
    _ ≤ _ := hRate

lemma exactCalibrationEndpoint_regret_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (q : Reservoir n m) {z : ℝ} (hz : 0≤z) :
    0≤optimalScalarValue P 1 z-(exactCalibrationEndpoint q z).scalarObjective P 1 z :=
  sub_nonneg.mpr (scalarObjective_le_optimal _ P hP zero_le_one hz)

lemma calibration_unnormalized_regret_coefficient_change (P : Instance n) (π : RandomizedPolicy n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z z' : ℝ} (hz : 0≤z) (hz' : 0≤z') :
    optimalScalarValue P 1 z-π.scalarObjective P 1 z ≤
      optimalScalarValue P 1 z'-π.scalarObjective P 1 z'+2*|z-z'| := by
  have hV := optimalScalarValue_durationWeight_lipschitz P hP zero_le_one hz hz'
  have hJ := π.scalarObjective_coefficients_lipschitz P hP 1 z' 1 z
  simp only [sub_self,abs_zero,mul_zero,zero_add,abs_sub_comm z' z] at hJ
  linarith only [(le_abs_self _).trans hV,(le_abs_self _).trans hJ]

end ProphetSecretary.Statistics.Calibration
