import ProphetSecretary.Limiting.DirectUnscaledIndividualScores
import ProphetSecretary.Stability.PositiveWeightScoreStability

/-!
# Uniform second moments and regret control for the actual direct scores

These are the variance and uniform competing-policy clauses of
`lem:score-expectations`. The tail profile and all score hypotheses are
proved for the actual schedule. Scalar weights are arbitrary positive fixed
weights. Literal centered bounded continuous scores retain their fixed norm
factor, while positive-band scores have information at most twice the band
intensity.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

 theorem directScheduled_cloud_score_secondMoment_le (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b) (m : ℕ) :
    (∫ x, (completeScore (B.directScheduledCloudScore hZero S m) x)^2
      ∂(B.directFiniteApproximation hZero m).valuesLaw)≤2*B.intensity.real S := by
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  have hProps := B.directScheduledCloudScore_properties hZero hS hS0 m
  exact (completeScore_secondMoment (B.directFiniteApproximation hZero m).law _ hProps.1
    (fun i => Eventually.of_forall (hProps.2.1 i)) hProps.2.2.1).trans_le
    (B.directScheduledCloudScore_information_le hZero hS hb hSub m)

 theorem directScheduled_unscaled_individual_secondMoment_le (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (m : ℕ) :
    (∫ x, (completeScore (B.directUnscaledIndividualScore hZero i f m) x)^2
      ∂(B.directFiniteApproximation hZero m).valuesLaw)≤(boundedScoreScale f)^2 := by
  let score := directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f
  have hProps := directIndividualScore_properties (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f
  have hMean : ∀ j, (∫ x, score j x ∂(B.directFiniteApproximation hZero m).law j)=0 := by
    rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact hProps.2.2.1
  have hInfo : information (B.directFiniteApproximation hZero m).law score≤1 := by
    rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact hProps.2.2.2
  have hSecond := (completeScore_secondMoment (B.directFiniteApproximation hZero m).law score hProps.1
    (fun j => Eventually.of_forall (hProps.2.1 j)) hMean).trans_le hInfo
  change (∫ x, (completeScore (fun j y => boundedScoreScale f*score j y) x)^2
    ∂(B.directFiniteApproximation hZero m).valuesLaw)≤(boundedScoreScale f)^2
  simp only [completeScore_const_mul,mul_pow,integral_const_mul]
  exact (mul_le_mul_of_nonneg_left hSecond (sq_nonneg (boundedScoreScale f))).trans_eq (mul_one _)

 theorem directScheduled_cloud_score_regret_stability (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    ∃ Ω : ℝ → ℝ, (∀ r, 0≤Ω r ∧ Ω r≤(B.cap:ℝ)+1) ∧ Monotone Ω ∧ Ω 0=0 ∧
      Tendsto Ω (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      Tendsto (fun r => Real.sqrt (2*(2*B.intensity.real S)*((B.cap:ℝ)+1)*Ω (r/(w+c))))
        (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      ∀ m (π : RandomizedPolicy (m+B.directVirtualCount hZero m)) (r : ℝ),
        Model.optimalScalarValue (B.directFiniteApproximation hZero m) w c-
          π.scalarObjective (B.directFiniteApproximation hZero m) w c≤r →
        |π.expectedRewardScore (B.directFiniteApproximation hZero m) (B.directScheduledCloudScore hZero S m)-
          (B.directCanonicalPolicy hZero hw hc m).expectedRewardScore (B.directFiniteApproximation hZero m) (B.directScheduledCloudScore hZero S m)|+
        |π.expectedDurationScore (B.directFiniteApproximation hZero m) (B.directScheduledCloudScore hZero S m)-
          (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore (B.directFiniteApproximation hZero m) (B.directScheduledCloudScore hZero S m)|≤
            Real.sqrt (2*(2*B.intensity.real S)*((B.cap:ℝ)+1)*Ω (r/(w+c))) := by
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  have hProps (m) := B.directScheduledCloudScore_properties hZero hS hS0 m
  exact finite_uniform_score_stability_positive_weights (fun m => m+B.directVirtualCount hZero m)
    (B.directFiniteApproximation hZero) B.cap.property (by positivity) hw hc (B.directFiniteApproximation_bounded hZero)
    (fun d => (B.totalTailMass d).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun m d hd => B.directFiniteApproximation_tailCount_le hZero m hd)
    (B.directScheduledCloudScore hZero S) (fun m => (hProps m).1)
    (fun m j => Eventually.of_forall ((hProps m).2.1 j)) (fun m => (hProps m).2.2.1)
    (B.directScheduledCloudScore_information_le hZero hS hb hSub)

 theorem directScheduled_unscaled_individual_regret_stability (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    ∃ Ω : ℝ → ℝ, (∀ r, 0≤Ω r ∧ Ω r≤(B.cap:ℝ)+1) ∧ Monotone Ω ∧ Ω 0=0 ∧
      Tendsto Ω (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      Tendsto (fun r => boundedScoreScale f*Real.sqrt (2*((B.cap:ℝ)+1)*Ω (r/(w+c))))
        (𝓝[>] (0:ℝ)) (𝓝 (0:ℝ)) ∧
      ∀ m (π : RandomizedPolicy (m+B.directVirtualCount hZero m)) (r : ℝ),
        Model.optimalScalarValue (B.directFiniteApproximation hZero m) w c-
          π.scalarObjective (B.directFiniteApproximation hZero m) w c≤r →
        |π.expectedRewardScore (B.directFiniteApproximation hZero m) (B.directUnscaledIndividualScore hZero i f m)-
          (B.directCanonicalPolicy hZero hw hc m).expectedRewardScore (B.directFiniteApproximation hZero m) (B.directUnscaledIndividualScore hZero i f m)|+
        |π.expectedDurationScore (B.directFiniteApproximation hZero m) (B.directUnscaledIndividualScore hZero i f m)-
          (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore (B.directFiniteApproximation hZero m) (B.directUnscaledIndividualScore hZero i f m)|≤
            boundedScoreScale f*Real.sqrt (2*((B.cap:ℝ)+1)*Ω (r/(w+c))) := by
  let score := fun m => directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f
  have hProps (m) := directIndividualScore_properties (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f
  have hMean (m) : ∀ j, (∫ x, score m j x ∂(B.directFiniteApproximation hZero m).law j)=0 := by
    rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact (hProps m).2.2.1
  have hInfo (m) : information (B.directFiniteApproximation hZero m).law (score m)≤1 := by
    rw [B.directFiniteApproximation_eq_appendVirtual hZero m]
    exact (hProps m).2.2.2
  obtain ⟨Ω,hΩ,hMono,hZeroΩ,hLim,hRoot,hScore⟩ := finite_uniform_score_stability_positive_weights
    (fun m => m+B.directVirtualCount hZero m) (B.directFiniteApproximation hZero) B.cap.property zero_le_one hw hc
    (B.directFiniteApproximation_bounded hZero) (fun d => (B.totalTailMass d).toReal) (fun _ _ => ENNReal.toReal_nonneg)
    (fun m d hd => B.directFiniteApproximation_tailCount_le hZero m hd) score (fun m => (hProps m).1)
    (fun m j => Eventually.of_forall ((hProps m).2.1 j)) hMean hInfo
  refine ⟨Ω,hΩ,hMono,hZeroΩ,hLim,?_,?_⟩
  · convert hRoot.const_mul (boundedScoreScale f) using 1
    · funext r
      simp only [mul_one]
      rfl
    · simp only [mul_zero]
  · intro m π r hr
    have h := mul_le_mul_of_nonneg_left (hScore m π r hr) (boundedScoreScale_positive f).le
    change |π.expectedRewardScore _ (fun j x => boundedScoreScale f*score m j x)-
      (B.directCanonicalPolicy hZero hw hc m).expectedRewardScore _ (fun j x => boundedScoreScale f*score m j x)|+
      |π.expectedDurationScore _ (fun j x => boundedScoreScale f*score m j x)-
      (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore _ (fun j x => boundedScoreScale f*score m j x)|≤_
    simp only [RandomizedPolicy.expectedRewardScore_const_mul,
      RandomizedPolicy.expectedDurationScore_const_mul,← mul_sub,abs_mul,
      abs_of_pos (boundedScoreScale_positive f)]
    rw [← mul_add]
    convert h using 1 <;> first | rfl | (simp only [mul_one]; rfl)
end ProphetSecretary.Limiting.CountableInstance
