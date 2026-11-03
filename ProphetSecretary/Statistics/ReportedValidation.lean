import ProphetSecretary.Statistics.CalibratedOfflineLaw
import ProphetSecretary.Statistics.DurationVectorCalibration

/-!
# Validation with reported stopping times

The first empirical block and target are unchanged. Each profile reports
the timestamp of the stopping rank, which may be rounded, before the same
finite interpolation is applied. The population error uses a fresh
trajectory under the same reported-duration rule.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [NeZero m]

noncomputable def reportedValidationDuration (report : ℝ → ℝ) (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) (j : Fin (J+1)) : ℝ :=
  report (validationDuration zlo zhi estimate q ω j)

lemma reportedValidationDuration_range (report : ℝ → ℝ)
    (hReport : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) 1)
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) (j : Fin (J+1)) :
    reportedValidationDuration report zlo zhi estimate q ω j∈Icc (0 : ℝ) 1 :=
  hReport _ (validationDuration_range zlo zhi estimate q ω j)

lemma reportedValidationDuration_monotone (report : ℝ → ℝ)
    (hReport : MonotoneOn report (Icc (0 : ℝ) 1))
    {zlo zhi : ℝ} (hz : zlo≤zhi) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) :
    Monotone (reportedValidationDuration report zlo zhi estimate q ω) := by
  intro i j hij
  exact hReport (validationDuration_range zlo zhi estimate q ω i) (validationDuration_range zlo zhi estimate q ω j)
    (validationDuration_monotone hz estimate q ω hij)

noncomputable def reportedOfflinePrepare (report : ℝ → ℝ) (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : OfflineData n m J TSeed PSeed) : PreparedCalibration n m :=
  let q := offlineEmpiricalBlock d
  let ρ := offlineTarget mu targetEstimate d
  (q,durationVectorSelection (reportedValidationDuration report zlo zhi policyEstimate q) d.2 ρ)

lemma reportedOfflinePrepare_id (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : OfflineData n m J TSeed PSeed) :
    reportedOfflinePrepare id mu zlo zhi targetEstimate policyEstimate d =
      offlinePrepare mu zlo zhi targetEstimate policyEstimate d := rfl

lemma reportedOfflinePrepare_bounds (report : ℝ → ℝ) (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : OfflineData n m J TSeed PSeed) :
    let p := (reportedOfflinePrepare report mu zlo zhi targetEstimate policyEstimate d).2
    1≤p.1 ∧ p.1≤J+2 ∧ p.2∈Ioc (0 : ℝ) 1 := by
  have h := computedTarget_range mu targetEstimate d.1.1 d.1.2
  exact durationVectorSelection_bounds _ d.2
    ⟨(by norm_num : (0 : ℝ)<1/2).trans_le h.1,h.2.trans (by norm_num)⟩

variable [MeasurableSpace TSeed] [MeasurableSpace PSeed]

lemma measurable_reportedOfflinePrepare (report : ℝ → ℝ) (hReport : Measurable report)
    (mu zlo zhi : ℝ) (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    Measurable (reportedOfflinePrepare (J := J) report mu zlo zhi targetEstimate policyEstimate) := by
  let D := OfflineData n m J TSeed PSeed
  let τ := fun (d : D) (a : Fin m) j => reportedValidationDuration report zlo zhi policyEstimate
    (offlineEmpiricalBlock d) (d.2 a) j
  have hτ (a : Fin m) (j : Fin (J+1)) : Measurable (fun d => τ d a j) :=
    hReport.comp (measurable_validationDuration zlo zhi policyEstimate hC
      measurable_offlineEmpiricalBlock ((measurable_pi_apply a).comp measurable_snd) j)
  have hS := measurable_durationVectorSelection hτ (measurable_offlineTarget mu targetEstimate hT)
  exact measurable_offlineEmpiricalBlock.prodMk hS

noncomputable def reportedOfflineError (P : Instance n) (νP : Measure PSeed)
    (report : ℝ → ℝ) (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : OfflineData n m J TSeed PSeed) : ℝ :=
  durationVectorError (P.worldLaw (policyQueryArrayLaw νP))
    (reportedValidationDuration report zlo zhi policyEstimate (offlineEmpiricalBlock d))
    (offlineTarget mu targetEstimate d) d.2

lemma measurable_reportedOfflineError (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP]
    (report : ℝ → ℝ) (hReport : Measurable report)
    (mu zlo zhi : ℝ) (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    Measurable (reportedOfflineError (J := J) P νP report mu zlo zhi targetEstimate policyEstimate) := by
  let D := OfflineData n m J TSeed PSeed
  let Y := World n (PolicyQueryArray n J PSeed)
  let τ := fun (d : D) (ω : Y) j =>
    reportedValidationDuration report zlo zhi policyEstimate (offlineEmpiricalBlock d) ω j
  let ρ := offlineTarget (J := J) (PSeed := PSeed) mu targetEstimate
  let θ := fun d : D => durationVectorParameter (τ d) d.2 (ρ d)
  have hAt (a : Fin m) (j : Fin (J+1)) : Measurable (fun d : D => τ d (d.2 a) j) :=
    hReport.comp (measurable_validationDuration zlo zhi policyEstimate hC
      measurable_offlineEmpiricalBlock ((measurable_pi_apply a).comp measurable_snd) j)
  have hv (k : ℕ) : Measurable (fun d : D => durationVectorAverage (τ d) d.2 k) := by
    apply Measurable.const_mul
    apply Finset.measurable_sum
    intro a _
    exact measurable_durationKnots (hAt a) k
  have hρ : Measurable ρ := measurable_offlineTarget mu targetEstimate hT
  have hθ : Measurable θ := measurable_selectionParameter _ _ _ hv hρ
  have hB (j : Fin (J+1)) : Measurable (fun d : D × Y => τ d.1 d.2 j) :=
    hReport.comp (measurable_validationDuration zlo zhi policyEstimate hC
      (measurable_offlineEmpiricalBlock.comp measurable_fst) measurable_snd j)
  have h := measurable_durationCurve (J+2) (fun k => measurable_durationKnots hB k)
    (hθ.comp measurable_fst)
  have hMean := (h.stronglyMeasurable.integral_prod_right'
    (ν:=P.worldLaw (policyQueryArrayLaw (J := J) νP))).measurable
  exact hMean.sub hρ

omit [MeasurableSpace TSeed] in
lemma reportedOfflineError_abs_le_one (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP]
    (report : ℝ → ℝ) (hReport : Measurable report)
    (hRange : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) 1)
    (hMono : MonotoneOn report (Icc (0 : ℝ) 1)) (mu : ℝ) {zlo zhi : ℝ} (hz : zlo≤zhi)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (d : OfflineData n m J TSeed PSeed) :
    |reportedOfflineError P νP report mu zlo zhi targetEstimate policyEstimate d|≤1 := by
  let Y := World n (PolicyQueryArray n J PSeed)
  let τ := reportedValidationDuration (J := J) report zlo zhi policyEstimate (offlineEmpiricalBlock d)
  let μ := P.worldLaw (policyQueryArrayLaw (n := n) (J := J) νP)
  let ρ := offlineTarget mu targetEstimate d
  let θ := durationVectorParameter τ d.2 ρ
  have ht (j : Fin (J+1)) : Measurable (fun y : Y => τ y j) :=
    hReport.comp (measurable_validationDuration zlo zhi policyEstimate hC
      (y := fun _ => offlineEmpiricalBlock d) (ω := id) measurable_const measurable_id j)
  have hF : Measurable (Function.uncurry (durationVectorCurve τ)) :=
    measurable_durationCurve (J+2)
      (fun k => measurable_durationKnots (fun j => (ht j).comp measurable_snd) k) measurable_fst
  have hR (y : Y) (j : Fin (J+1)) : τ y j∈Icc (0 : ℝ) 1 :=
    reportedValidationDuration_range report hRange zlo zhi policyEstimate (offlineEmpiricalBlock d) y j
  have hM (y : Y) : Monotone (τ y) :=
    reportedValidationDuration_monotone report hMono hz policyEstimate (offlineEmpiricalBlock d) y
  have hC' (t : ℝ) (y : Y) : durationVectorCurve τ t y∈Icc (0 : ℝ) 1 :=
    durationCurve_range _ _ (durationKnots_monotone _ (hM y) (hR y))
      (durationKnots_zero _) (durationKnots_last _) t
  have hU := populationCurve_range μ (durationVectorCurve τ) hF hC' θ
  have hρ : ρ∈Icc (0 : ℝ) 1 := by
    have h := computedTarget_range mu targetEstimate d.1.1 d.1.2
    exact ⟨(by norm_num : (0 : ℝ)≤1/2).trans h.1,h.2.trans (by norm_num)⟩
  apply abs_le.mpr
  change -(1 : ℝ)≤populationCurve μ (durationVectorCurve τ) θ-ρ ∧
    populationCurve μ (durationVectorCurve τ) θ-ρ≤1
  exact ⟨by linarith [hU.1,hρ.2],by linarith [hU.2,hρ.1]⟩

theorem reportedOfflineError_moments (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (report : ℝ → ℝ) (hReport : Measurable report)
    (hRange : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) 1)
    (hMono : MonotoneOn report (Icc (0 : ℝ) 1)) (mu : ℝ) {zlo zhi : ℝ} (hz : zlo≤zhi)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    let g := reportedOfflineError (J := J) P νP report mu zlo zhi targetEstimate policyEstimate
    let O := offlineDataLaw (m := m) (J := J) P νT νP
    |∫ d,g d ∂O|≤1/((m : ℝ)+1) ∧ (∫ d,(g d)^2 ∂O)≤4/(m : ℝ) := by
  let g := reportedOfflineError (J := J) P νP report mu zlo zhi targetEstimate policyEstimate
  let I := firstInformationLaw (m := m) P νT
  let W := validationWorldArrayLaw (m := m) (J := J) P νP
  have hg := measurable_reportedOfflineError (J := J) P νP report hReport mu zlo zhi targetEstimate policyEstimate hT hC
  have hgB := reportedOfflineError_abs_le_one (J := J) P νP report hReport hRange hMono mu hz targetEstimate policyEstimate hC
  have hgI : Integrable g (I.prod W) := Integrable.of_bound hg.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun d => by simpa only [Real.norm_eq_abs] using hgB d)
  have hg2I : Integrable (fun d => (g d)^2) (I.prod W) :=
    Integrable.of_bound (hg.pow_const 2).aestronglyMeasurable 1
      (Filter.Eventually.of_forall fun d => by
        rw [Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
        simpa only [sq_abs,one_pow] using pow_le_pow_left₀ (abs_nonneg (g d)) (hgB d) 2)
  have hMom (p : FirstInformation n m TSeed) :
      |∫ w,g (p,w) ∂W|≤1/((m : ℝ)+1) ∧ (∫ w,(g (p,w))^2 ∂W)≤4/(m : ℝ) := by
    let q := reservoirCoordinates.symm p.1
    let τ := reportedValidationDuration (J := J) report zlo zhi policyEstimate q
    let ρ := computedTarget mu targetEstimate p.1 p.2
    let Y := World n (PolicyQueryArray n J PSeed)
    let μ := P.worldLaw (policyQueryArrayLaw (n := n) (J := J) νP)
    have hτ (j : Fin (J+1)) : Measurable (fun y : Y => τ y j) :=
      hReport.comp (measurable_validationDuration zlo zhi policyEstimate hC
        (y := fun _ => q) (ω := id) measurable_const measurable_id j)
    have hR := computedTarget_range mu targetEstimate p.1 p.2
    have hρ : ρ∈Ioc (0 : ℝ) 1 := ⟨(by norm_num : (0 : ℝ)<1/2).trans_le hR.1,hR.2.trans (by norm_num)⟩
    have h := durationVectorError_moments (m := m) μ τ hτ
      (reportedValidationDuration_monotone report hMono hz policyEstimate q)
      (reportedValidationDuration_range report hRange zlo zhi policyEstimate q) hρ
    simpa only [g,W,reportedOfflineError,validationWorldArrayLaw,offlineEmpiricalBlock,offlineTarget] using h
  change |∫ d,g d ∂I.prod W|≤1/((m : ℝ)+1) ∧ (∫ d,(g d)^2 ∂I.prod W)≤4/(m : ℝ)
  constructor
  · rw [integral_prod _ hgI]
    apply abs_integral_le_integral_abs.trans
    have h := integral_mono hgI.integral_prod_left.abs (integrable_const (1/((m : ℝ)+1))) (fun d => (hMom d).1)
    simpa only [integral_const,probReal_univ,one_smul] using h
  · rw [integral_prod _ hg2I]
    have h := integral_mono hg2I.integral_prod_left (integrable_const (4/(m : ℝ))) (fun d => (hMom d).2)
    simpa only [integral_const,probReal_univ,one_smul] using h

end ProphetSecretary.Statistics.Calibration
