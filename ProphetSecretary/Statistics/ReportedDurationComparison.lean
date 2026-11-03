import ProphetSecretary.Statistics.ReportedValidation
import ProphetSecretary.Statistics.CalibratedSelectorExecution
import ProphetSecretary.Statistics.CalibrationMasterPointwise

/-!
# Transfer from reported durations to actual stopping times

Downward rounding changes a duration knot by at most the clock mesh. On
interior segments the selected surrogate loses at most the mesh; the two
artificial endpoint extensions retain their one-sided comparisons.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [NeZero m]

lemma durationKnots_report_error (report : ℝ → ℝ) {δ : ℝ} (hδ : 0≤δ)
    (hr : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) t ∧ t-report t≤δ)
    (τ : Fin (J+1) → ℝ) (hτ : ∀ j, τ j∈Icc (0 : ℝ) 1) (k : ℕ) :
    durationKnots (report ∘ τ) k≤durationKnots τ k ∧
      durationKnots τ k≤durationKnots (report ∘ τ) k+δ := by
  by_cases h0 : k=0
  · simp only [durationKnots,if_pos h0]
    constructor <;> linarith
  · by_cases hk : k≤J+1
    · let j : Fin (J+1) := ⟨k-1,by omega⟩
      have h := hr (τ j) (hτ j)
      simp only [durationKnots,if_neg h0,dif_pos hk,Function.comp_def]
      change report (τ j)≤τ j ∧ τ j≤report (τ j)+δ
      exact ⟨h.1.2,by linarith only [h.2]⟩
    · simp only [durationKnots,if_neg h0,dif_neg hk]
      constructor <;> linarith

lemma durationCurve_report_error (report : ℝ → ℝ) {δ : ℝ} (hδ : 0≤δ)
    (hr : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) t ∧ t-report t≤δ)
    (τ : Fin (J+1) → ℝ) (hτ : ∀ j, τ j∈Icc (0 : ℝ) 1)
    {k : ℕ} (hk0 : 1≤k) (hk1 : k≤J+2) {α : ℝ} (hα : α∈Icc (0 : ℝ) 1) :
    let θ := (((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ)
    durationCurve (J+2) (durationKnots (report ∘ τ)) θ≤durationCurve (J+2) (durationKnots τ) θ ∧
      durationCurve (J+2) (durationKnots τ) θ≤durationCurve (J+2) (durationKnots (report ∘ τ)) θ+δ := by
  dsimp only
  rw [durationCurve_on_segment (J+2) (by omega) _ (k-1) (by omega) hα,
    durationCurve_on_segment (J+2) (by omega) (durationKnots τ) (k-1) (by omega) hα,
    show k-1+1=k by omega]
  have h0 := durationKnots_report_error report hδ hr τ hτ (k-1)
  have h1 := durationKnots_report_error report hδ hr τ hτ k
  have hβ : 0≤1-α := sub_nonneg.mpr hα.2
  refine ⟨add_le_add (mul_le_mul_of_nonneg_left h0.1 hβ) (mul_le_mul_of_nonneg_left h1.1 hα.1),?_⟩
  have h := add_le_add (mul_le_mul_of_nonneg_left h0.2 hβ) (mul_le_mul_of_nonneg_left h1.2 hα.1)
  linarith only [h]

variable [MeasurableSpace PSeed]

theorem reportedOffline_duration_comparison (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP]
    (report : ℝ → ℝ) (hReport : Measurable report) {δ : ℝ} (hδ : 0≤δ)
    (hr : ∀ t∈Icc (0 : ℝ) 1, report t∈Icc (0 : ℝ) t ∧ t-report t≤δ)
    (hMono : MonotoneOn report (Icc (0 : ℝ) 1))
    (mu : ℝ) {zlo zhi : ℝ} (hz : zlo≤zhi)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (d : OfflineData n m J TSeed PSeed) :
    let A := reportedOfflinePrepare report mu zlo zhi targetEstimate policyEstimate
    let k := (A d).2.1
    let T := (selectorConditionalPolicy νP zlo zhi policyEstimate A hC d).expectedDuration P
    let U := offlineTarget mu targetEstimate d+
      reportedOfflineError P νP report mu zlo zhi targetEstimate policyEstimate d
    (k≠1 → T≤U+δ) ∧ T≥U-(if k=J+2 then 1 else 0) := by
  let A := reportedOfflinePrepare (J := J) report mu zlo zhi targetEstimate policyEstimate
  let p := A d
  let q := offlineEmpiricalBlock d
  let k := p.2.1
  let α := p.2.2
  let θ := (((k-1 : ℕ) : ℝ)+α)/(J+2 : ℕ)
  let Y := World n (PolicyQueryArray n J PSeed)
  let ν := P.worldLaw (policyQueryArrayLaw (n := n) (J := J) νP)
  let τ := validationDuration (J := J) zlo zhi policyEstimate q
  let f := durationVectorCurve τ θ
  let g := durationVectorCurve (reportedValidationDuration (J := J) report zlo zhi policyEstimate q) θ
  let T := (selectorConditionalPolicy νP zlo zhi policyEstimate A hC d).expectedDuration P
  let U := ∫ y,g y ∂ν
  let V := ∫ y,f y ∂ν
  obtain ⟨hk0,hk1,hα⟩ := reportedOfflinePrepare_bounds report mu zlo zhi targetEstimate policyEstimate d
  change 1≤k at hk0
  change k≤J+2 at hk1
  have hα' : α∈Icc (0 : ℝ) 1 := ⟨hα.1.le,hα.2⟩
  have ht (j : Fin (J+1)) : Measurable (fun y : Y => τ y j) :=
    measurable_validationDuration zlo zhi policyEstimate hC (y := fun _ => q) (ω := id)
      measurable_const measurable_id j
  have hf : Measurable f := measurable_durationCurve (J+2)
    (fun l => measurable_durationKnots ht l) measurable_const
  have hg : Measurable g := measurable_durationCurve (J+2)
    (fun l => measurable_durationKnots (fun j => hReport.comp (ht j)) l) measurable_const
  have hτ (y : Y) (j : Fin (J+1)) : τ y j∈Icc (0 : ℝ) 1 :=
    validationDuration_range zlo zhi policyEstimate q y j
  have hfR (y : Y) : f y∈Icc (0 : ℝ) 1 := profileCurve_range hz policyEstimate q y θ
  have hgR (y : Y) : g y∈Icc (0 : ℝ) 1 := by
    have hm := reportedValidationDuration_monotone report hMono hz policyEstimate q y
    have hR (j : Fin (J+1)) : reportedValidationDuration report zlo zhi policyEstimate q y j∈Icc (0 : ℝ) 1 :=
      ⟨(hr _ (hτ y j)).1.1,(hr _ (hτ y j)).1.2.trans (hτ y j).2⟩
    exact durationCurve_range _ _ (durationKnots_monotone _ hm hR)
      (durationKnots_zero _) (durationKnots_last _) θ
  have hfI : Integrable f ν := Integrable.of_bound hf.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (hfR y).1]; exact (hfR y).2)
  have hgI : Integrable g ν := Integrable.of_bound hg.aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun y => by rw [Real.norm_eq_abs,abs_of_nonneg (hgR y).1]; exact (hgR y).2)
  have hPt (y : Y) : g y≤f y ∧ f y≤g y+δ := durationCurve_report_error report hδ hr (τ y) (hτ y) hk0 hk1 hα'
  have hUV : U≤V := integral_mono hgI hfI (fun y => (hPt y).1)
  have hVU : V≤U+δ := by
    have h := integral_mono hfI (hgI.add (integrable_const δ)) (fun y => (hPt y).2)
    change V≤∫ y,g y+δ ∂ν at h
    rwa [integral_add hgI (integrable_const δ),integral_const,probReal_univ,one_smul] at h
  have hCases : (k=1 → V≤T) ∧ (2≤k → k≤J+1 → V=T) ∧ (k=J+2 → T≤V) :=
    preparedPolicy_duration_comparison (J := J) P νP zlo zhi policyEstimate hC q hk0 hk1 hα'
  have hDef : offlineTarget mu targetEstimate d+
      reportedOfflineError P νP report mu zlo zhi targetEstimate policyEstimate d=U := by
    let ρ := offlineTarget mu targetEstimate d
    change ρ+(U-ρ)=U
    ring
  dsimp only
  rw [hDef]
  change (k≠1 → T≤U+δ) ∧ T≥U-(if k=J+2 then 1 else 0)
  constructor
  · intro hl
    by_cases hr : k=J+2
    · exact (hCases.2.2 hr).trans hVU
    · exact (hCases.2.1 (by omega) (by omega)).ge.trans hVU
  · by_cases hr : k=J+2
    · rw [if_pos hr]
      have hU : U≤1 := by
        have h := integral_mono hgI (integrable_const (1 : ℝ)) (fun y => (hgR y).2)
        simpa only [U,integral_const,probReal_univ,one_smul] using h
      have hT := (selectorConditionalPolicy νP zlo zhi policyEstimate A hC d).expectedDuration_nonnegative P
      change 0≤T at hT
      linarith only [hU,hT]
    · rw [if_neg hr,sub_zero]
      by_cases hl : k=1
      · exact hUV.trans (hCases.1 hl)
      · exact hUV.trans (hCases.2.1 (by omega) (by omega)).le

/-- The mesh changes the nonleft reward master inequality by at most one quarter of its width. -/
theorem calibration_reward_master_nonleft_reported (P : Instance n) (π : RandomizedPolicy n)
    (hP : P.HasPositiveFiniteMaximum) {mu z g ρ r δ : ℝ} (hM : mu≤P.expectedMaximum)
    (hM1 : P.expectedMaximum≤1) (hz : z∈Icc (0 : ℝ) (1/4)) (hδ : 0≤δ)
    (hReg : optimalScalarValue P 1 z-π.scalarObjective P 1 z≤r)
    (hTime : π.expectedDuration P≤ρ+g+δ) :
    mu*normalizedScalarGap P (normalizedCoefficient z)-r-z*g-
      (1/4)*max 0 (ρ-P.optimalScalarRatio)-δ/4 ≤
        π.expectedReward P-optimalCompetitiveRatio*P.expectedMaximum := by
  have h := calibration_reward_master_nonleft P π hP hM hM1 hz hReg
    (ρ := ρ) (g := g+δ) (by simpa only [add_assoc] using hTime)
  linarith only [h,mul_le_mul_of_nonneg_right hz.2 hδ]

end ProphetSecretary.Statistics.Calibration
