import ProphetSecretary.Statistics.CalibratedValidationProfiles
import ProphetSecretary.Statistics.CalibratedSelection
import ProphetSecretary.Statistics.CalibrationConcentration

/-!
# The actual validation selector and its calibration moments

The finite first-crossing scan uses the empirical mean of the concrete shared
policy-duration knots. Its interpolated point equals the least root used in
the independent-sample calibration theorem. The signed error retains the
whole selected point, including endpoint-extension fractions.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} [NeZero m] {PSeed : Type*}

noncomputable def meanDurationKnots (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) (k : ℕ) : ℝ :=
  (m : ℝ)⁻¹*∑ a, durationKnots (validationDuration zlo zhi estimate y (w a)) k

lemma meanDurationKnots_monotone {zlo zhi : ℝ} (hz : zlo ≤ zhi)
    (estimate : ContinuationEstimator n m PSeed) (y : Reservoir n m)
    (w : Fin m → World n (PolicyQueryArray n J PSeed)) : Monotone (meanDurationKnots zlo zhi estimate y w) := by
  intro k l hkl
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ =>
    durationKnots_monotone _ (validationDuration_monotone hz estimate y (w a))
      (validationDuration_range zlo zhi estimate y (w a)) hkl)) (by positivity)

lemma meanDurationKnots_zero (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) :
    meanDurationKnots zlo zhi estimate y w 0=0 := by simp [meanDurationKnots]

lemma meanDurationKnots_last (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) :
    meanDurationKnots zlo zhi estimate y w (J+2)=1 := by
  simp only [meanDurationKnots,durationKnots_last, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, mul_one]
  exact inv_mul_cancel₀ (by exact_mod_cast NeZero.ne m)

lemma empiricalProfileCurve_eq (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) (θ : ℝ) :
    empiricalCurve (fun θ ω => profileCurve zlo zhi estimate y ω θ) w θ =
      durationCurve (J+2) (meanDurationKnots zlo zhi estimate y w) θ := by
  exact (durationCurve_average (J+2) m
    (fun a => durationKnots (validationDuration zlo zhi estimate y (w a))) θ).symm

/-- The pair used by the actual endpoint-mixture decision, before the online run. -/
noncomputable def validationSelection (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) (ρ : ℝ) : ℕ × ℝ :=
  (calibrationCrossing (meanDurationKnots zlo zhi estimate y w) ρ (J+2),
    calibrationMixingFraction (meanDurationKnots zlo zhi estimate y w) ρ (J+2))

noncomputable def validationSelectionPoint (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) (ρ : ℝ) : ℝ :=
  selectionParameter (J+2) (meanDurationKnots zlo zhi estimate y w) ρ

lemma validationSelection_bounds (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed))
    {ρ : ℝ} (hρ : ρ ∈ Ioc (0 : ℝ) 1) :
    1 ≤ (validationSelection zlo zhi estimate y w ρ).1 ∧
    (validationSelection zlo zhi estimate y w ρ).1 ≤ J+2 ∧
    (validationSelection zlo zhi estimate y w ρ).2 ∈ Ioc (0 : ℝ) 1 := by
  have h0 : meanDurationKnots zlo zhi estimate y w 0 < ρ := by rw [meanDurationKnots_zero];exact hρ.1
  have h1 : ρ ≤ meanDurationKnots zlo zhi estimate y w (J+2) := by rw [meanDurationKnots_last];exact hρ.2
  have h := calibrationCrossing_bounds (meanDurationKnots zlo zhi estimate y w) ρ (J+2) h0 h1
  exact ⟨h.1,h.2.1,calibrationMixingFraction_mem_unit _ _ _ h0 h1⟩

lemma validationSelectionPoint_eq_parameter {zlo zhi : ℝ} (hz : zlo ≤ zhi)
    (estimate : ContinuationEstimator n m PSeed) (y : Reservoir n m)
    (w : Fin m → World n (PolicyQueryArray n J PSeed)) {ρ : ℝ} (hρ : ρ ∈ Ioc (0 : ℝ) 1) :
    validationSelectionPoint zlo zhi estimate y w ρ =
      parameter (fun θ ω => profileCurve zlo zhi estimate y ω θ) ρ w := by
  have h := selectionParameter_eq_leastRoot (J+2) (by omega) (meanDurationKnots zlo zhi estimate y w)
    (meanDurationKnots_monotone hz estimate y w) (meanDurationKnots_zero zlo zhi estimate y w)
    (meanDurationKnots_last zlo zhi estimate y w) hρ
  have hF : durationCurve (J+2) (meanDurationKnots zlo zhi estimate y w) =
      empiricalCurve (fun θ ω => profileCurve zlo zhi estimate y ω θ) w := by
    funext θ
    exact (empiricalProfileCurve_eq zlo zhi estimate y w θ).symm
  rw [hF] at h
  exact h

lemma measurable_meanDurationKnots [MeasurableSpace PSeed] {Ω : Type*} [MeasurableSpace Ω]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    {y : Ω → Reservoir n m} {w : Ω → Fin m → World n (PolicyQueryArray n J PSeed)}
    (hy : Measurable y) (hw : Measurable w) (k : ℕ) :
    Measurable (fun p => meanDurationKnots zlo zhi estimate (y p) (w p) k) := by
  apply Measurable.const_mul
  apply Finset.measurable_sum
  intro a _
  exact measurable_durationKnots (fun j => measurable_validationDuration zlo zhi estimate hEstimate
    hy ((measurable_pi_apply a).comp hw) j) k

lemma measurable_validationSelection [MeasurableSpace PSeed] {Ω : Type*} [MeasurableSpace Ω]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    {y : Ω → Reservoir n m} {w : Ω → Fin m → World n (PolicyQueryArray n J PSeed)} {ρ : Ω → ℝ}
    (hy : Measurable y) (hw : Measurable w) (hρ : Measurable ρ) :
    Measurable (fun p => validationSelection zlo zhi estimate (y p) (w p) (ρ p)) := by
  exact (measurable_calibrationCrossing _ _ _ (fun k => measurable_meanDurationKnots
    zlo zhi estimate hEstimate hy hw k) hρ).prodMk
      (measurable_calibrationMixingFraction _ _ _ (fun k => measurable_meanDurationKnots
        zlo zhi estimate hEstimate hy hw k) hρ)

/-- The analytical signed error uses the whole selected surrogate point. -/
noncomputable def validationSelectionError [MeasurableSpace PSeed]
    (P : Instance n) (νP : Measure PSeed) (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (ρ : ℝ) (w : Fin m → World n (PolicyQueryArray n J PSeed)) : ℝ :=
  (∫ ω : World n (PolicyQueryArray n J PSeed),
    profileCurve zlo zhi estimate y ω (validationSelectionPoint zlo zhi estimate y w ρ)
      ∂P.worldLaw (policyQueryArrayLaw (n := n) (J := J) νP))-ρ

lemma validationSelectionError_eq_calibrationError [MeasurableSpace PSeed]
    (P : Instance n) (νP : Measure PSeed) {zlo zhi : ℝ} (hz : zlo ≤ zhi)
    (estimate : ContinuationEstimator n m PSeed) (y : Reservoir n m)
    {ρ : ℝ} (hρ : ρ ∈ Ioc (0 : ℝ) 1) :
    validationSelectionError (m := m) (J := J) P νP zlo zhi estimate y ρ =
      error (P.worldLaw (policyQueryArrayLaw (J := J) νP)) (fun θ ω => profileCurve zlo zhi estimate y ω θ) ρ := by
  funext w
  unfold validationSelectionError error populationCurve
  rw [validationSelectionPoint_eq_parameter hz estimate y w hρ]

lemma measurable_validationSelectionPoint [MeasurableSpace PSeed] {Ω : Type*} [MeasurableSpace Ω]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    {y : Ω → Reservoir n m} {w : Ω → Fin m → World n (PolicyQueryArray n J PSeed)} {ρ : Ω → ℝ}
    (hy : Measurable y) (hw : Measurable w) (hρ : Measurable ρ) :
    Measurable (fun p => validationSelectionPoint zlo zhi estimate (y p) (w p) (ρ p)) :=
  measurable_selectionParameter _ _ _ (fun k => measurable_meanDurationKnots
    zlo zhi estimate hEstimate hy hw k) hρ

/-- The actual finite validation selector has the paper's signed bias and square-error bounds. -/
theorem validationSelection_error_moments [MeasurableSpace PSeed]
    (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP]
    {zlo zhi : ℝ} (hz : zlo ≤ zhi) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) (y : Reservoir n m)
    {ρ : ℝ} (hρ : ρ ∈ Ioc (0 : ℝ) 1) :
    |∫ w, validationSelectionError (m := m) (J := J) P νP zlo zhi estimate y ρ w
      ∂Measure.pi (fun _ : Fin m => P.worldLaw (policyQueryArrayLaw (J := J) νP))| ≤ 1/((m : ℝ)+1) ∧
    (∫ w, (validationSelectionError (m := m) (J := J) P νP zlo zhi estimate y ρ w)^2
      ∂Measure.pi (fun _ : Fin m => P.worldLaw (policyQueryArrayLaw (J := J) νP))) ≤ 4/(m : ℝ) := by
  let Y := World n (PolicyQueryArray n J PSeed)
  let μ := P.worldLaw (policyQueryArrayLaw (n := n) (J := J) νP)
  let f : ℝ → Y → ℝ := fun θ ω => profileCurve zlo zhi estimate y ω θ
  have hf : Measurable (Function.uncurry f) :=
    measurable_profileCurve zlo zhi estimate hEstimate (y := fun _ : ℝ × Y => y)
      (ω := Prod.snd) (θ := Prod.fst) measurable_const measurable_snd measurable_fst
  have hc : ∀ ω : Y, Continuous (fun θ => f θ ω) := fun ω => profileCurve_continuous _ _ _ y ω
  have hm : ∀ ω : Y, Monotone (fun θ => f θ ω) := fun ω => profileCurve_monotone hz estimate y ω
  have hr : ∀ θ (ω : Y), f θ ω ∈ Icc (0 : ℝ) 1 := fun θ ω => profileCurve_range hz estimate y ω θ
  have h0 : ∀ ω : Y, f 0 ω=0 := fun ω => (profileCurve_endpoints _ _ _ y ω).1
  have h1 : ∀ ω : Y, f 1 ω=1 := fun ω => (profileCurve_endpoints _ _ _ y ω).2
  rw [validationSelectionError_eq_calibrationError P νP hz estimate y hρ]
  exact ⟨integral_error_abs_le μ f hf hc hm hr h0 h1 ⟨hρ.1.le,hρ.2⟩,
    integral_error_sq_le μ f hf hc hm hr h0 h1 ⟨hρ.1.le,hρ.2⟩⟩

lemma measurable_validationSelectionError [MeasurableSpace PSeed] {Ω : Type*} [MeasurableSpace Ω]
    (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    {y : Ω → Reservoir n m} {w : Ω → Fin m → World n (PolicyQueryArray n J PSeed)} {ρ : Ω → ℝ}
    (hy : Measurable y) (hw : Measurable w) (hρ : Measurable ρ) :
    Measurable (fun p => validationSelectionError P νP zlo zhi estimate (y p) (ρ p) (w p)) := by
  let Y := World n (PolicyQueryArray n J PSeed)
  have hPoint := measurable_validationSelectionPoint zlo zhi estimate hEstimate hy hw hρ
  have hF : Measurable (fun q : Ω × Y => profileCurve zlo zhi estimate (y q.1) q.2
      (validationSelectionPoint zlo zhi estimate (y q.1) (w q.1) (ρ q.1))) :=
    measurable_profileCurve zlo zhi estimate hEstimate (hy.comp measurable_fst) measurable_snd
      (hPoint.comp measurable_fst)
  exact hF.stronglyMeasurable.integral_prod_right'.measurable.sub hρ

lemma validationSelectionError_abs_le_one [MeasurableSpace PSeed]
    (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP]
    {zlo zhi : ℝ} (hz : zlo ≤ zhi) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)) (y : Reservoir n m)
    {ρ : ℝ} (hρ : ρ ∈ Icc (0 : ℝ) 1) (w : Fin m → World n (PolicyQueryArray n J PSeed)) :
    |validationSelectionError P νP zlo zhi estimate y ρ w| ≤ 1 := by
  let Y := World n (PolicyQueryArray n J PSeed)
  let μ := P.worldLaw (policyQueryArrayLaw (n := n) (J := J) νP)
  let f : ℝ → Y → ℝ := fun θ ω => profileCurve zlo zhi estimate y ω θ
  have hf : Measurable (Function.uncurry f) :=
    measurable_profileCurve zlo zhi estimate hEstimate (y := fun _ : ℝ × Y => y)
      (ω := Prod.snd) (θ := Prod.fst) measurable_const measurable_snd measurable_fst
  have hPop := populationCurve_range μ f hf (fun θ ω => profileCurve_range hz estimate y ω θ)
    (validationSelectionPoint zlo zhi estimate y w ρ)
  change |populationCurve μ f (validationSelectionPoint zlo zhi estimate y w ρ)-ρ| ≤ 1
  exact abs_le.mpr ⟨by linarith [hPop.1,hρ.2],by linarith [hPop.2,hρ.1]⟩

end ProphetSecretary.Statistics.Calibration
