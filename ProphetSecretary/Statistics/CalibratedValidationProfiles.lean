import ProphetSecretary.Statistics.CalibratedPolicyFamily
import ProphetSecretary.Statistics.CalibratedDurationCurve

/-!
# Actual validation duration profiles and their surrogate curves

Every profile is simulated using the same query array for every coefficient.
Clamping raw clocks makes its durations lie in `[0,1]` everywhere; under the
actual uniform-clock law the clamp changes nothing. Zero-valued arrivals
remain in each policy's observed history and seed-position count.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} [NeZero m] {PSeed : Type*}

noncomputable def validationDuration (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) (j : Fin (J+1)) : ℝ :=
  (numericalFamilyPolicy zlo zhi estimate j).stoppingTime (y,ω.2.2) Finset.univ ω.1
    (fun i => unitRamp (ω.2.1 i))

lemma validationDuration_range (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) (j : Fin (J+1)) :
    validationDuration zlo zhi estimate y ω j ∈ Icc (0 : ℝ) 1 :=
  ⟨Policy.stoppingTime_nonneg _ _ _ _ _ (fun _ => (unitRamp_range _).1),
    Policy.stoppingTime_le_one _ _ _ _ _⟩

lemma validationDuration_monotone {zlo zhi : ℝ} (hz : zlo ≤ zhi)
    (estimate : ContinuationEstimator n m PSeed) (y : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) : Monotone (validationDuration zlo zhi estimate y ω) := by
  intro j k hjk
  exact numericalFamilyPolicy_stoppingTime_mono hz estimate hjk _ _ _ _

lemma validationDuration_eq_actual (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) (j : Fin (J+1))
    (hu : ∀ i, ω.2.1 i ∈ Icc (0 : ℝ) 1) :
    validationDuration zlo zhi estimate y ω j =
      (numericalFamilyPolicy zlo zhi estimate j).stoppingTime (y,ω.2.2) Finset.univ ω.1 ω.2.1 := by
  have he : (fun i => unitRamp (ω.2.1 i))=ω.2.1 := funext (fun i => unitRamp_eq (hu i))
  unfold validationDuration
  rw [he]

lemma measurable_validationDuration [MeasurableSpace PSeed] {Ω : Type*} [MeasurableSpace Ω]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    {y : Ω → Reservoir n m} {ω : Ω → World n (PolicyQueryArray n J PSeed)}
    (hy : Measurable y) (hω : Measurable ω) (j : Fin (J+1)) :
    Measurable (fun p => validationDuration zlo zhi estimate (y p) (ω p) j) := by
  exact Policy.measurable_stoppingTime _ (numericalFamilyPolicy_isMeasurable zlo zhi estimate hEstimate j)
    (hy.prodMk (measurable_snd.comp (measurable_snd.comp hω)))
    (fun i => (measurable_pi_apply i).comp (measurable_fst.comp hω))
    (fun i => continuous_unitRamp.measurable.comp
      ((measurable_pi_apply i).comp (measurable_fst.comp (measurable_snd.comp hω)))) Finset.univ

/-- Add the two endpoint-extension knots to the actual policy durations. -/
def durationKnots (τ : Fin (J+1) → ℝ) (k : ℕ) : ℝ :=
  if k=0 then 0 else if hk : k ≤ J+1 then τ ⟨k-1,by omega⟩ else 1

@[simp] lemma durationKnots_zero (τ : Fin (J+1) → ℝ) : durationKnots τ 0=0 := by simp [durationKnots]

@[simp] lemma durationKnots_last (τ : Fin (J+1) → ℝ) : durationKnots τ (J+2)=1 := by
  simp [durationKnots]

lemma durationKnots_range (τ : Fin (J+1) → ℝ) (hτ : ∀ j, τ j ∈ Icc (0 : ℝ) 1) (k : ℕ) :
    durationKnots τ k ∈ Icc (0 : ℝ) 1 := by
  unfold durationKnots
  split_ifs <;> simp_all

lemma durationKnots_monotone (τ : Fin (J+1) → ℝ) (hτ : Monotone τ)
    (hrange : ∀ j, τ j ∈ Icc (0 : ℝ) 1) : Monotone (durationKnots τ) := by
  intro k l hkl
  by_cases hk : k=0
  · rw [hk,durationKnots_zero]
    exact (durationKnots_range τ hrange l).1
  · by_cases hl : l ≤ J+1
    · have hl0 : l ≠ 0 := by omega
      have hkJ : k ≤ J+1 := hkl.trans hl
      simp only [durationKnots, if_neg hk, if_neg hl0, dif_pos hkJ, dif_pos hl]
      exact hτ (by change k-1 ≤ l-1; omega)
    · have hl0 : l ≠ 0 := by omega
      have he : durationKnots τ l=1 := by simp [durationKnots,hl,hl0]
      rw [he]
      exact (durationKnots_range τ hrange k).2

lemma measurable_durationKnots {Ω : Type*} [MeasurableSpace Ω]
    {τ : Ω → Fin (J+1) → ℝ} (hτ : ∀ j, Measurable (fun p => τ p j)) (k : ℕ) :
    Measurable (fun p => durationKnots (τ p) k) := by
  unfold durationKnots
  split_ifs
  · exact measurable_const
  · exact hτ _
  · exact measurable_const

noncomputable def profileCurve (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) (θ : ℝ) : ℝ :=
  durationCurve (J+2) (durationKnots (validationDuration zlo zhi estimate y ω)) θ

lemma profileCurve_continuous (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) :
    Continuous (profileCurve zlo zhi estimate y ω) := durationCurve_continuous _ _

lemma profileCurve_monotone {zlo zhi : ℝ} (hz : zlo ≤ zhi)
    (estimate : ContinuationEstimator n m PSeed) (y : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) : Monotone (profileCurve zlo zhi estimate y ω) :=
  durationCurve_monotone _ _ (durationKnots_monotone _ (validationDuration_monotone hz estimate y ω)
    (validationDuration_range zlo zhi estimate y ω))

lemma profileCurve_endpoints (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (y : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) :
    profileCurve zlo zhi estimate y ω 0=0 ∧ profileCurve zlo zhi estimate y ω 1=1 := by
  constructor
  · rw [profileCurve,durationCurve_zero,durationKnots_zero]
  · rw [profileCurve,durationCurve_one,durationKnots_last]

lemma profileCurve_range {zlo zhi : ℝ} (hz : zlo ≤ zhi)
    (estimate : ContinuationEstimator n m PSeed) (y : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) (θ : ℝ) :
    profileCurve zlo zhi estimate y ω θ ∈ Icc (0 : ℝ) 1 :=
  durationCurve_range _ _ (durationKnots_monotone _ (validationDuration_monotone hz estimate y ω)
    (validationDuration_range zlo zhi estimate y ω)) (durationKnots_zero _) (durationKnots_last _) θ

lemma measurable_profileCurve [MeasurableSpace PSeed] {Ω : Type*} [MeasurableSpace Ω]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (hEstimate : Measurable (fun q : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2))
    {y : Ω → Reservoir n m} {ω : Ω → World n (PolicyQueryArray n J PSeed)} {θ : Ω → ℝ}
    (hy : Measurable y) (hω : Measurable ω) (hθ : Measurable θ) :
    Measurable (fun p => profileCurve zlo zhi estimate (y p) (ω p) (θ p)) := by
  exact measurable_durationCurve _ (fun k => measurable_durationKnots
    (fun j => measurable_validationDuration zlo zhi estimate hEstimate hy hω j) k) hθ

end ProphetSecretary.Statistics.Calibration
