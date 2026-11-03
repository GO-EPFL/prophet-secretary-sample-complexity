import ProphetSecretary.Statistics.ReportedValidation
import ProphetSecretary.Statistics.CalibratedRightExtension

/-!
# The right extension with reported validation times

A clock mesh of at most (1/20) still leaves a positive separation between
the last expected duration and the largest allowed target. This gives a
uniform exponential bound for selecting the right extension.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [NeZero m]

lemma durationVectorSelection_right_implies_mean_lt {Y : Type*}
    (τ : Y → Fin (J+1) → ℝ) (w : Fin m → Y) {ρ : ℝ} (hρ : ρ∈Ioc (0 : ℝ) 1)
    (hRight : (durationVectorSelection τ w ρ).1=J+2) :
    (m : ℝ)⁻¹*∑ a, τ (w a) (Fin.last J)<ρ := by
  let v := durationVectorAverage τ w
  have h0 : v 0<ρ := by simpa only [v,durationVectorAverage_zero] using hρ.1
  have h1 : ρ≤v (J+2) := by simpa only [v,durationVectorAverage_last] using hρ.2
  have h := (calibrationCrossing_bounds v ρ (J+2) h0 h1).2.2.1
  change calibrationCrossing v ρ (J+2)=J+2 at hRight
  rw [hRight,show J+2-1=J+1 by omega] at h
  change (m : ℝ)⁻¹*∑ a, durationKnots (τ (w a)) (J+1)<ρ at h
  have hEq (a : Fin m) : durationKnots (τ (w a)) (J+1)=τ (w a) (Fin.last J) := by
    rw [durationKnots_upper_eq _ (by omega) le_rfl]
    congr 1
    apply Fin.ext
    simp [upperPolicyIndex]
  simpa only [hEq] using h

variable [MeasurableSpace PSeed]

lemma reportedValidation_right_probability_le (P : Instance n) (νP : Measure PSeed)
    [IsProbabilityMeasure νP] (hP : Integrable Instance.maximum P.valuesLaw) (hM : P.expectedMaximum≤1/80)
    (report : ℝ → ℝ) (hReport : Measurable report) {δ : ℝ} (hδ : δ≤1/20)
    (hr : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) t ∧ t-report t≤δ)
    {zlo : ℝ} (h0 : 0≤zlo) (hz : zlo≤1/4) (hJ : 0<J)
    (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (q : Reservoir n m) {ρ : ℝ} (hρ : ρ∈Ioc (0 : ℝ) (4/5)) :
    (validationWorldArrayLaw (m := m) (J := J) P νP).real
      {w | (durationVectorSelection (reportedValidationDuration report zlo (1/4) estimate q) w ρ).1=J+2} ≤
        Real.exp (-(m : ℝ)/200) := by
  let Y := World n (PolicyQueryArray n J PSeed)
  let ν := P.worldLaw (policyQueryArrayLaw (n := n) (J := J) νP)
  let τ : Y → Fin (J+1) → ℝ := validationDuration zlo (1/4) estimate q
  let f := fun y : Y => τ y (Fin.last J)
  let g := fun y : Y => report (f y)
  have hf : Measurable f := measurable_validationDuration zlo (1/4) estimate he
    (y := fun _ => q) (ω := id) measurable_const measurable_id _
  have hg : Measurable g := hReport.comp hf
  have hfR (y : Y) : f y∈Icc (0 : ℝ) 1 := validationDuration_range zlo (1/4) estimate q y _
  have hgR (y : Y) : g y∈Icc (0 : ℝ) 1 := ⟨(hr _ (hfR y)).1.1,(hr _ (hfR y)).1.2.trans (hfR y).2⟩
  have hfI : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (hfR y).1]; exact (hfR y).2)
  have hgI : Integrable g ν := Integrable.of_bound hg.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (hgR y).1]; exact (hgR y).2)
  have hDrift := integral_mono (hfI.sub hgI) (integrable_const δ) (fun y => (hr _ (hfR y)).2)
  have hDrift' : (∫ y,f y ∂ν)-(∫ y,g y ∂ν)≤δ := by
    change (∫ y,f y-g y ∂ν)≤∫ _,δ ∂ν at hDrift
    have hEq : (∫ y,f y-g y ∂ν)=(∫ y,f y ∂ν)-(∫ y,g y ∂ν) :=
      integral_sub hfI hgI
    rw [hEq] at hDrift
    simpa only [integral_const,probReal_univ,one_smul] using hDrift
  have hLast : (19/20 : ℝ)≤∫ y,f y ∂ν :=
    last_validationDuration_mean_ge P νP hP hM h0 hz hJ estimate he q
  have hMean : (9/10 : ℝ)≤∫ y,g y ∂ν := by linarith only [hLast,hDrift',hδ]
  let F := fun (_ : ℝ) (y : Y) => g y
  have hF : Measurable (Function.uncurry F) := hg.comp measurable_snd
  have hT := empiricalCurve_lower_tail (m := m) ν F hF (fun _ y => hgR y) 0
    (show (0 : ℝ)≤1/10 by norm_num)
  have hInc : {w : Fin m → Y | (durationVectorSelection
      (reportedValidationDuration report zlo (1/4) estimate q) w ρ).1=J+2} ⊆
      {w | empiricalCurve F w 0≤populationCurve ν F 0-1/10} := by
    intro w hw
    have hρ' : ρ∈Ioc (0 : ℝ) 1 := ⟨hρ.1,hρ.2.trans (by norm_num)⟩
    have h := durationVectorSelection_right_implies_mean_lt
      (reportedValidationDuration report zlo (1/4) estimate q) w hρ' hw
    change (m : ℝ)⁻¹*∑ a,g (w a)<ρ at h
    change (m : ℝ)⁻¹*∑ a,g (w a)≤(∫ y,g y ∂ν)-1/10
    linarith only [h,hMean,hρ.2]
  exact (measureReal_mono (μ := validationWorldArrayLaw (m := m) (J := J) P νP) hInc).trans
    (by simpa only [validationWorldArrayLaw,ν,show -(m : ℝ)*(1/10)^2/2=-(m : ℝ)/200 by ring] using hT)

variable [MeasurableSpace TSeed]

theorem reportedOffline_right_probability_le (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (hP : Integrable Instance.maximum P.valuesLaw) (hM : P.expectedMaximum≤1/80)
    (report : ℝ → ℝ) (hReport : Measurable report) {δ : ℝ} (hδ : δ≤1/20)
    (hr : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) t ∧ t-report t≤δ)
    {zlo : ℝ} (h0 : 0≤zlo) (hz : zlo≤1/4) (hJ : 0<J)
    (mu : ℝ) (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    (offlineDataLaw (m := m) (J := J) P νT νP).real
      {d | (reportedOfflinePrepare report mu zlo (1/4) targetEstimate policyEstimate d).2.1=J+2} ≤
        Real.exp (-(m : ℝ)/200) := by
  let D := OfflineData n m J TSeed PSeed
  let A := {d : D | (reportedOfflinePrepare report mu zlo (1/4) targetEstimate policyEstimate d).2.1=J+2}
  let F := A.indicator (1 : D → ℝ)
  have hA : MeasurableSet A := measurableSet_eq_fun
    (measurable_fst.comp (measurable_snd.comp
      (measurable_reportedOfflinePrepare report hReport mu zlo (1/4) targetEstimate policyEstimate hT hC))) measurable_const
  let I := firstInformationLaw (m := m) P νT
  let W := validationWorldArrayLaw (m := m) (J := J) P νP
  have hI : Integrable F (I.prod W) := (integrable_const (1 : ℝ)).indicator hA
  have hF (p : FirstInformation n m TSeed) :
      (∫ w,F (p,w) ∂W)≤Real.exp (-(m : ℝ)/200) := by
    let Fst (w : ValidationWorldArray n m J PSeed) : D := (p,w)
    let B := Fst ⁻¹' A
    have hB : MeasurableSet B := hA.preimage (show Measurable Fst from measurable_const.prodMk measurable_id)
    have hEq : (fun w => F (p,w))=B.indicator (1 : ValidationWorldArray n m J PSeed → ℝ) := rfl
    rw [hEq,integral_indicator_one hB]
    have hR := computedTarget_range mu targetEstimate p.1 p.2
    have hRight := reportedValidation_right_probability_le (J := J) P νP hP hM report hReport hδ hr h0 hz hJ
      policyEstimate hC (reservoirCoordinates.symm p.1)
      (ρ := computedTarget mu targetEstimate p.1 p.2)
      ⟨(by norm_num : (0 : ℝ)<1/2).trans_le hR.1,hR.2⟩
    simpa only [B,Fst,A,Set.preimage_setOf_eq,reportedOfflinePrepare,offlineEmpiricalBlock,offlineTarget] using hRight
  change (I.prod W).real A≤_
  rw [← integral_indicator_one hA]
  change (∫ d,F d ∂I.prod W)≤_
  rw [integral_prod _ hI]
  have h := integral_mono hI.integral_prod_left (integrable_const (Real.exp (-(m : ℝ)/200))) hF
  simpa only [integral_const,probReal_univ,one_smul] using h

end ProphetSecretary.Statistics.Calibration
