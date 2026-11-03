import ProphetSecretary.Statistics.CalibratedConditioning
import ProphetSecretary.Statistics.CalibratedOfflineStatistics
import ProphetSecretary.Statistics.CalibrationRationalEndpoint

/-!
# Scalar regret and duration at the actual selected point

On the left extension the executed first policy is charged normalized
regret at the clamp endpoint. Other points use unnormalized regret at the
selected coefficient. Surrogate duration always retains the full point.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

section

variable (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (mu zlo : ℝ) (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "D" => OfflineData n m J TSeed PSeed
local notation "O" => offlineDataLaw (m := m) (J := J) P νT νP
local notation "A" => offlinePrepare (J := J) mu zlo (1/4) targetEstimate policyEstimate
local notation "C" => conditionalCalibrationPolicy (J := J) νP mu zlo (1/4) targetEstimate policyEstimate hC
local notation "g" => offlineCalibrationError (J := J) P νP mu zlo (1/4) targetEstimate policyEstimate
local notation "ρ" => offlineTarget (J := J) (PSeed := PSeed) mu targetEstimate

noncomputable def offlineSelectedCoefficient (d : D) : ℝ :=
  selectedCoefficient zlo (1/4) J (A d).2

local notation "Z" => offlineSelectedCoefficient (J := J) mu zlo targetEstimate policyEstimate

include hT hC in
lemma measurable_offlineSelectedCoefficient : Measurable Z := by
  classical
  let k := fun d : D => (A d).2.1
  let α := fun d : D => (A d).2.2
  have hA := measurable_offlinePrepare (J := J) mu zlo (1/4) targetEstimate policyEstimate hT hC
  have hk : Measurable k := measurable_fst.comp (measurable_snd.comp hA)
  have hα : Measurable α := measurable_snd.comp (measurable_snd.comp hA)
  have hLow := (measurable_of_countable
    (fun j : ℕ => familyCoefficient zlo (1/4) J (lowerPolicyIndex J j).val)).comp hk
  have hHi := (measurable_of_countable
    (fun j : ℕ => familyCoefficient zlo (1/4) J (upperPolicyIndex J j).val)).comp hk
  have hK : MeasurableSet {d : D | k d=1} := measurableSet_eq_fun hk measurable_const
  have hB := (((measurable_const (a := (1 : ℝ))).sub hα).mul hLow).add (hα.mul hHi)
  change Measurable (fun d : D => if k d=1 then (0 : ℝ) else
    (1-α d)*familyCoefficient zlo (1/4) J (lowerPolicyIndex J (k d)).val+
      α d*familyCoefficient zlo (1/4) J (upperPolicyIndex J (k d)).val)
  apply Measurable.ite hK measurable_const
  convert hB using 1
  funext d
  rfl

omit [MeasurableSpace TSeed] [MeasurableSpace PSeed] in
lemma offlineSelectedCoefficient_range (h0 : 0≤zlo) (hz : zlo≤1/4) (d : D) :
    Z d∈Icc (0 : ℝ) (1/4) :=
  selectedCoefficient_range h0 hz J _ ⟨(offlinePrepare_bounds mu zlo (1/4) targetEstimate policyEstimate d).2.2.1.le,
    (offlinePrepare_bounds mu zlo (1/4) targetEstimate policyEstimate d).2.2.2⟩

omit [MeasurableSpace TSeed] [MeasurableSpace PSeed] in
lemma offlineSelectedCoefficient_left (d : D) (hl : (A d).2.1=1) : Z d=0 := by
  simp only [offlineSelectedCoefficient,selectedCoefficient,hl,if_true]

noncomputable def offlineSelectedRegret (b : ℝ) (d : D) : ℝ :=
  if (A d).2.1=1 then (C d).normalizedRegret P b
  else optimalScalarValue P 1 (Z d)-(C d).scalarObjective P 1 (Z d)

local notation "r" => offlineSelectedRegret (J := J) P νP mu zlo targetEstimate policyEstimate hC

omit [MeasurableSpace TSeed] in
lemma offlineSelectedRegret_nonnegative (hP : Integrable Instance.maximum P.valuesLaw)
    (h0 : 0≤zlo) (hz : zlo≤1/4) {b : ℝ} (hb : b∈Icc (0 : ℝ) 1) (d : D) :
    0≤r b d := by
  unfold offlineSelectedRegret
  split_ifs
  · exact (C d).normalizedRegret_nonnegative P hP hb
  · exact sub_nonneg.mpr (scalarObjective_le_optimal (C d) P hP zero_le_one
      (offlineSelectedCoefficient_range mu zlo targetEstimate policyEstimate h0 hz d).1)

include hT in
lemma integrable_offlineSelectedRegret (hP : Integrable Instance.maximum P.valuesLaw)
    (h0 : 0≤zlo) (hz : zlo≤1/4) {b : ℝ} (hb : b∈Icc (0 : ℝ) 1) :
    Integrable (r b) O := by
  have hRI := integrable_conditionalCalibrationReward (J := J) P νT νP mu zlo (1/4)
    targetEstimate policyEstimate hT hC hP
  have hTI := integrable_conditionalCalibrationDuration (J := J) P νT νP mu zlo (1/4)
    targetEstimate policyEstimate hT hC
  have hA := measurable_offlinePrepare (J := J) mu zlo (1/4) targetEstimate policyEstimate hT hC
  have hZ := measurable_offlineSelectedCoefficient (J := J) mu zlo targetEstimate policyEstimate hT hC
  have hZrange := offlineSelectedCoefficient_range (J := J) mu zlo targetEstimate policyEstimate h0 hz
  have hV := P.measurable_scalarValue_coefficients hP (measurable_const (a := (1 : ℝ))) hZ
    (fun _ => zero_le_one) (fun d => (hZrange d).1)
  have hVb : AEMeasurable (fun _ : D => optimalScalarValue P b (1-b)) O := aemeasurable_const
  have hLeft := hVb.sub
    ((hRI.aemeasurable.const_mul b).add (hTI.aemeasurable.const_mul (1-b)))
  have hMid := hV.aemeasurable.sub (hRI.aemeasurable.add (hZ.aemeasurable.mul hTI.aemeasurable))
  have hK : MeasurableSet {d : D | (A d).2.1=1} :=
    measurableSet_eq_fun (measurable_fst.comp (measurable_snd.comp hA)) measurable_const
  have hR : AEMeasurable (r b) O := by
    change AEMeasurable (fun d : D => r b d) O
    simp only [offlineSelectedRegret,RandomizedPolicy.normalizedRegret,
      RandomizedPolicy.scalarObjective_eq _ P hP,one_mul]
    let L := hLeft.mk _
    let U := hMid.mk _
    have hm : Measurable (fun d : D => if (A d).2.1=1 then L d else U d) :=
      Measurable.ite hK hLeft.measurable_mk hMid.measurable_mk
    apply hm.aemeasurable.congr
    filter_upwards [hLeft.ae_eq_mk,hMid.ae_eq_mk] with d hL hU
    by_cases hd : (A d).2.1=1
    · simpa only [if_pos hd,L,Pi.sub_apply,Pi.add_apply] using hL.symm
    · simpa only [if_neg hd,U,Pi.sub_apply,Pi.add_apply,Pi.mul_apply] using hU.symm
  apply Integrable.of_bound hR.aestronglyMeasurable (P.expectedMaximum+1)
  exact Filter.Eventually.of_forall fun d => by
    rw [Real.norm_eq_abs,abs_of_nonneg
      (offlineSelectedRegret_nonnegative P νP mu zlo targetEstimate policyEstimate hC hP h0 hz hb d)]
    unfold offlineSelectedRegret
    split_ifs
    · unfold RandomizedPolicy.normalizedRegret
      have hVb := optimalScalarValue_le_benchmark P hP hb.1 (sub_nonneg.mpr hb.2)
      have hJ := (C d).scalarObjective_nonnegative P hP hb.1 (sub_nonneg.mpr hb.2)
      linarith only [hVb,hJ,mul_le_of_le_one_left P.expectedMaximum_nonnegative hb.2,hb.1]
    · have hVb := optimalScalarValue_le_benchmark P hP zero_le_one (hZrange d).1
      have hJ := (C d).scalarObjective_nonnegative P hP zero_le_one (hZrange d).1
      linarith only [hVb,hJ,(hZrange d).2]

omit [MeasurableSpace TSeed] in
lemma offline_duration_comparison (hz : zlo≤1/4) (d : D) :
    let k := (A d).2.1
    let T := (C d).expectedDuration P
    let U := ρ d+g d
    (k=1 → U≤T) ∧ (2≤k → k≤J+1 → U=T) ∧ (k=J+2 → T≤U) ∧
      T≥U-(if k=J+2 then 1 else 0) := by
  let k := (A d).2.1
  let α := (A d).2.2
  let q := offlineEmpiricalBlock d
  let ν := policyQueryArrayLaw (n := n) (J := J) νP
  let T := (C d).expectedDuration P
  let U := ρ d+g d
  obtain ⟨hk0,hk1,hα⟩ := offlinePrepare_bounds mu zlo (1/4) targetEstimate policyEstimate d
  have hComp := preparedPolicy_duration_comparison P νP zlo (1/4) policyEstimate hC q hk0 hk1
    (show α∈Icc (0 : ℝ) 1 from ⟨hα.1.le,hα.2⟩)
  have hU : U=(∫ ω : World n (PolicyQueryArray n J PSeed),
      profileCurve zlo (1/4) policyEstimate q ω ((((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ)) ∂P.worldLaw ν) := by
    unfold U offlineCalibrationError offlineTarget
    have hTheta : validationSelectionPoint zlo (1/4) policyEstimate q d.2
        (computedTarget mu targetEstimate d.1.1 d.1.2)=((((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ)) := rfl
    change _+((∫ ω : World n (PolicyQueryArray n J PSeed),
      profileCurve zlo (1/4) policyEstimate q ω
        (validationSelectionPoint zlo (1/4) policyEstimate q d.2 (computedTarget mu targetEstimate d.1.1 d.1.2))
      ∂P.worldLaw ν)-computedTarget mu targetEstimate d.1.1 d.1.2)=_
    rw [hTheta]
    ring
  have hCases : (k=1 → U≤T) ∧ (2≤k → k≤J+1 → U=T) ∧ (k=J+2 → T≤U) := by
    rw [hU]
    exact hComp
  change (k=1 → U≤T) ∧ (2≤k → k≤J+1 → U=T) ∧ (k=J+2 → T≤U) ∧
    T≥U-(if k=J+2 then 1 else 0)
  refine ⟨hCases.1,hCases.2.1,hCases.2.2,?_⟩
  by_cases hRight : k=J+2
  · rw [if_pos hRight]
    have hT0 := (C d).expectedDuration_nonnegative P
    have hU1 : U≤1 := by
      rw [hU]
      have hm : Measurable (fun ω : World n (PolicyQueryArray n J PSeed) =>
          profileCurve zlo (1/4) policyEstimate q ω ((((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ))) :=
        measurable_profileCurve zlo (1/4) policyEstimate hC
        (y := fun _ : World n (PolicyQueryArray n J PSeed) => q) (ω := id)
        (θ := fun _ => ((((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ))) measurable_const measurable_id measurable_const
      have hRange (ω : World n (PolicyQueryArray n J PSeed)) := profileCurve_range hz policyEstimate q ω ((((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ))
      have hI := Integrable.of_bound (μ := P.worldLaw ν) hm.aestronglyMeasurable 1
        (Filter.Eventually.of_forall fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (hRange ω).1]; exact (hRange ω).2)
      have hi := integral_mono hI (integrable_const (1 : ℝ)) (fun ω => (hRange ω).2)
      simpa only [integral_const,probReal_univ,one_smul] using hi
    linarith
  · rw [if_neg hRight,sub_zero]
    by_cases hLeft : k=1
    · exact hCases.1 hLeft
    · exact (hCases.2.1 (by omega) (by omega)).le

omit [MeasurableSpace TSeed] in
theorem offline_calibration_reward_master (hP : P.HasPositiveFiniteMaximum)
    {b : ℝ} (hb : b∈Icc (0 : ℝ) 1) (h0 : 0≤zlo) (hz : zlo≤1/4)
    (hMu : mu≤1/40) (hMean : mu≤P.expectedMaximum) (hM : P.expectedMaximum≤1)
    (hClamp : ∀ (π : RandomizedPolicy n) (x : ℝ), π.normalizedRegret P b≤x →
      normalizedScalarGap P 1/40-5*x≤π.expectedReward P-optimalCompetitiveRatio*P.expectedMaximum)
    (d : D) :
    mu*normalizedScalarGap P (normalizedCoefficient (Z d))-5*r b d-Z d*g d-
      (1/4)*max 0 (ρ d-P.optimalScalarRatio) ≤ (C d).expectedReward P-optimalCompetitiveRatio*P.expectedMaximum := by
  have hR0 := offlineSelectedRegret_nonnegative P νP mu zlo targetEstimate policyEstimate hC hP.1 h0 hz hb d
  by_cases hLeft : (A d).2.1=1
  · have hZ := offlineSelectedCoefficient_left mu zlo targetEstimate policyEstimate d hLeft
    have hReg : (C d).normalizedRegret P b≤r b d := by simp only [offlineSelectedRegret,hLeft,if_true,le_rfl]
    have h := calibration_reward_master_left P (C d) hP hMu (hClamp _ _ hReg)
    rw [hZ,zero_mul,sub_zero]
    linarith only [h,mul_nonneg (by norm_num : (0 : ℝ)≤1/4) (le_max_left (0 : ℝ) (ρ d-P.optimalScalarRatio))]
  · have hReg : optimalScalarValue P 1 (Z d)-(C d).scalarObjective P 1 (Z d)≤r b d := by
      simp only [offlineSelectedRegret,hLeft,if_false,le_rfl]
    have hComp := offline_duration_comparison (J := J) P νP mu zlo targetEstimate policyEstimate hC hz d
    have hBounds := offlinePrepare_bounds mu zlo (1/4) targetEstimate policyEstimate d
    have hTime : (C d).expectedDuration P≤ρ d+g d := by
      by_cases hRight : (A d).2.1=J+2
      · exact hComp.2.2.1 hRight
      · exact (hComp.2.1 (by omega) (by omega)).ge
    have h := calibration_reward_master_nonleft P (C d) hP hMean hM
      (offlineSelectedCoefficient_range mu zlo targetEstimate policyEstimate h0 hz d) hReg hTime
    linarith only [h,hR0]

end

end ProphetSecretary.Statistics.Calibration
