import ProphetSecretary.Statistics.ReportedDurationComparison
import ProphetSecretary.Statistics.ReportedRightExtension
import ProphetSecretary.Statistics.CalibratedReachGuarantee

/-!
# Reach with reported validation timestamps

Downward reporting can only help the duration comparison on the left and
interior segments. The right-extension probability remains exponentially
small under the actual reported profiles.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

lemma reported_right_exponential_le (m : ℕ) [NeZero m] :
    Real.exp (-(m : ℝ)/200)≤200/(m : ℝ) := by
  have hm : (0 : ℝ)<m := Nat.cast_pos.mpr (NeZero.pos m)
  have hX : 0<(m : ℝ)/200 := by positivity
  have hExp : (m : ℝ)/200≤Real.exp ((m : ℝ)/200) := by
    linarith [Real.add_one_le_exp ((m : ℝ)/200)]
  rw [show -(m : ℝ)/200 = -((m : ℝ)/200) by ring,Real.exp_neg]
  have h := inv_le_inv₀ (Real.exp_pos _) hX |>.mpr hExp
  refine h.trans_eq ?_
  field_simp

theorem reportedSelector_reach_of_conditional_comparison (P : Instance n)
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    {mu zlo : ℝ} (hmu : 0<mu) (h0 : 0≤zlo) (hz : zlo≤1/4) (hJ : 0<J)
    (hP : Integrable Instance.maximum P.valuesLaw) (hM : P.expectedMaximum≤1/80)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (report : ℝ → ℝ) (hReport : Measurable report) {δ : ℝ} (hδ : 0≤δ) (hδSmall : δ≤1/20)
    (hr : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) t ∧ t-report t≤δ)
    (hMono : MonotoneOn report (Icc (0 : ℝ) 1))
    (hConf : ∀ᵐ a ∂P.trainingCoordinateLaw m, targetEligible mu a → ∀ j : TargetGrid m,
      νT.real {r | 1/(m : ℝ) < |targetEstimate (reservoirCoordinates.symm a) (targetGrid j) r-
        optimalScalarValue (trainingInstance a) 1 (targetGrid j)|} ≤ 1/((m : ℝ)^2*(4*(m : ℝ)+1)))
    (i : Fin n)
    (hReach : ∀ᵐ d ∂offlineDataLaw (m := m) (J := J) P νT νP,
      let π := selectorConditionalPolicy νP zlo (1/4) policyEstimate
        (reportedOfflinePrepare report mu zlo (1/4) targetEstimate policyEstimate) hC d
      π.expectedDuration P-6/(m : ℝ)≤π.rule.reachProbability P (onlineCalibrationSeedLaw νP) i) :
    let A := reportedOfflinePrepare (J := J) report mu zlo (1/4) targetEstimate policyEstimate
    let hA := measurable_reportedOfflinePrepare (J := J) report hReport mu zlo (1/4)
      targetEstimate policyEstimate hT hC
    optimalCompetitiveRatio-208/(m : ℝ)≤
      (selectorLearner νT νP zlo (1/4) policyEstimate A hA hC).reachProbability P i := by
  let O := offlineDataLaw (m := m) (J := J) P νT νP
  let S := reportedOfflinePrepare (J := J) report mu zlo (1/4) targetEstimate policyEstimate
  let hS := measurable_reportedOfflinePrepare (J := J) report hReport mu zlo (1/4) targetEstimate policyEstimate hT hC
  let C := selectorConditionalPolicy νP zlo (1/4) policyEstimate S hC
  have hR (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : report t∈Icc (0 : ℝ) 1 :=
    ⟨(hr t ht).1.1,(hr t ht).1.2.trans ht.2⟩
  let N := onlineCalibrationSeedLaw (n := n) (J := J) νP
  let D := OfflineData n m J TSeed PSeed
  let T := fun d : D => (C d).expectedDuration P
  let q := fun d : D => (C d).rule.reachProbability P N i
  let ρ := offlineTarget (J := J) (PSeed := PSeed) mu targetEstimate
  let g := reportedOfflineError (J := J) P νP report mu zlo (1/4) targetEstimate policyEstimate
  let A := {d : D | (S d).2.1=J+2}
  let a := A.indicator (fun _ : D => (1 : ℝ))
  have hA : MeasurableSet A := measurableSet_eq_fun
    (measurable_fst.comp (measurable_snd.comp
      hS)) measurable_const
  have hAI : Integrable a O := (integrable_const (1 : ℝ)).indicator hA
  have hRI : Integrable ρ O := by
    apply Integrable.of_bound (measurable_offlineTarget mu targetEstimate hT).aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun d : D => by
      have h := computedTarget_range mu targetEstimate d.1.1 d.1.2
      change ‖computedTarget mu targetEstimate d.1.1 d.1.2‖≤1
      rw [Real.norm_eq_abs,abs_of_nonneg ((by norm_num : (0 : ℝ)≤1/2).trans h.1)]
      linarith [h.2]
  have hg : Measurable g := measurable_reportedOfflineError (J := J) P νP report hReport mu zlo (1/4) targetEstimate policyEstimate hT hC
  have hgI : Integrable g O := by
    apply Integrable.of_bound hg.aestronglyMeasurable 1
    exact Filter.Eventually.of_forall fun d => by
      rw [Real.norm_eq_abs]
      exact reportedOfflineError_abs_le_one P νP report hReport hR hMono mu hz targetEstimate policyEstimate hC d
  have hqI : Integrable q O := integrable_selectorConditionalReach P νT νP zlo (1/4) policyEstimate S hS hC i
  have hPt : ∀ᵐ d ∂O, ρ d+g d-a d-6/(m : ℝ)≤q d := by
    filter_upwards [hReach] with d hd
    have hC' := (reportedOffline_duration_comparison P νP report hReport hδ hr hMono mu hz targetEstimate policyEstimate hC d).2
    change T d≥ρ d+g d-(if d∈A then 1 else 0) at hC'
    have he : a d=(if d∈A then 1 else 0) := by by_cases h : d∈A <;> simp [a,h]
    rw [← he] at hC'
    change T d-6/(m : ℝ)≤q d at hd
    linarith only [hd,hC']
  have hI := integral_mono_ae ((((hRI.add hgI).sub hAI).sub (integrable_const (6/(m : ℝ))))) hqI hPt
  change (∫ d, ρ d+g d-a d-6/(m : ℝ) ∂O)≤∫ d,q d ∂O at hI
  rw [integral_sub (f := fun d => ρ d+g d-a d) (g := fun _ => 6/(m : ℝ))
      ((hRI.add hgI).sub hAI) (integrable_const (6/(m : ℝ))),
    integral_sub (f := fun d => ρ d+g d) (g := a) (hRI.add hgI) hAI,
    integral_add hRI hgI,integral_const,probReal_univ,one_smul] at hI
  have hTarget := numericalTarget_expected_lower_of_query_confidence (P.trainingCoordinateLaw m)
    (targetQueryArrayLaw νT) mu hmu _ (measurable_targetTable mu targetEstimate hT)
    (targetTable_conditional_confidence P νT mu targetEstimate hT hConf)
  have hRho := offlineTarget_integral (J := J) P νT νP mu targetEstimate hT id measurable_id
  simp only [id_eq,firstInformationLaw] at hRho
  change (∫ d, ρ d ∂O)=_ at hRho
  rw [← hRho] at hTarget
  have hG : |∫ d,g d ∂O|≤1/((m : ℝ)+1) :=
    (reportedOfflineError_moments (J := J) P νT νP report hReport hR hMono mu hz targetEstimate policyEstimate hT hC).1
  have hB := (reportedOffline_right_probability_le (J := J) P νT νP hP hM report hReport hδSmall hr h0 hz hJ
    mu targetEstimate policyEstimate hT hC).trans
    (reported_right_exponential_le m)
  change (O).real A≤_ at hB
  have hAmean : (∫ d,a d ∂O)=(O).real A := integral_indicator_one hA
  rw [hAmean] at hI
  have hm : (0 : ℝ)<m := Nat.cast_pos.mpr (NeZero.pos m)
  have hmOne : (1 : ℝ)≤m := by exact_mod_cast NeZero.pos m
  have hSmall : 1/(m : ℝ)^2≤1/(m : ℝ) :=
    one_div_le_one_div_of_le hm (by nlinarith)
  have hBias := (neg_abs_le (∫ d,g d ∂O))
  have hBias' := one_div_le_one_div_of_le hm (show (m : ℝ)≤(m : ℝ)+1 by linarith)
  change optimalCompetitiveRatio-208/(m : ℝ)≤(selectorLearner νT νP zlo (1/4) policyEstimate S hS hC).reachProbability P i
  rw [selectorLearner_reachProbability_eq_integral P νT νP zlo (1/4) policyEstimate S hS hC i]
  change optimalCompetitiveRatio-208/(m : ℝ)≤∫ d,q d ∂O
  have hG' : -(1/(m : ℝ))≤∫ d,g d ∂O := by linarith only [hG,hBias,hBias']
  have hR' : optimalCompetitiveRatio-1/(m : ℝ)≤∫ d,ρ d ∂O :=
    (sub_le_sub_left hSmall _).trans hTarget
  calc
    _ = (optimalCompetitiveRatio-1/(m : ℝ)) + (-(1/(m : ℝ))) - 200/(m : ℝ)-6/(m : ℝ) := by ring
    _ ≤ (∫ d,ρ d ∂O)+(∫ d,g d ∂O)-(O).real A-6/(m : ℝ) :=
      sub_le_sub_right (sub_le_sub (add_le_add hR' hG') hB) _
    _ ≤ _ := hI

end ProphetSecretary.Statistics.Calibration
