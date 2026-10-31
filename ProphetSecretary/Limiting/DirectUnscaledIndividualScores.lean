import ProphetSecretary.Limiting.DirectPositiveWeightScores
import ProphetSecretary.Limiting.DirectScheduledIndividualCoarse
import ProphetSecretary.Probability.ScoreRescalingIntegral

/-!
# Literal centered bounded continuous individual scores

The likelihood calculations use a unit-normalized score. Multiplication by
its fixed positive scale recovers the original centered observable, with no
change to the policy. The resulting complete-vector correlations therefore
cover every bounded continuous individual score in the manuscript.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def directUnscaledIndividualScore (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (m : ℕ) : Fin (m+B.directVirtualCount hZero m) → ℝ → ℝ :=
  fun j x => boundedScoreScale f*directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f j x

lemma directUnscaledIndividualScore_complete (B : CountableInstance) (hZero : B.terminal=0)
    (i : ℕ) (f : ℝ →ᵇ ℝ) (m : ℕ) (x : Fin (m+B.directVirtualCount hZero m) → ℝ) :
    completeScore (B.directUnscaledIndividualScore hZero i f m) x=
      if hi : i<m then f (x ((⟨i,hi⟩:Fin m).castAdd (B.directVirtualCount hZero m)))-
        ∫ y, f y ∂(B.individuals i:Measure ℝ) else 0 := by
  change completeScore (fun j y => boundedScoreScale f*directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f j y) x=_
  rw [completeScore_const_mul,directIndividualScore_complete]
  split_ifs with hi
  · exact boundedScoreScale_mul_centeredBoundedScore _ f _
  · exact mul_zero _

 theorem directScheduled_unscaled_individual_score_limits
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (i : ℕ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedRewardScore (B.directFiniteApproximation hZero m)
      (B.directUnscaledIndividualScore hZero i f m)) atTop
      (𝓝 (∫ v : CompleteWorld Unit, (f (v.2.1 i)-∫ x, f x ∂(B.individuals i:Measure ℝ))*
        (B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore (B.directFiniteApproximation hZero m)
      (B.directUnscaledIndividualScore hZero i f m)) atTop
      (𝓝 (∫ v : CompleteWorld Unit, (f (v.2.1 i)-∫ x, f x ∂(B.individuals i:Measure ℝ))*
        (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (B.directFiniteApproximation hZero m).expectedMaximumScore
      (B.directUnscaledIndividualScore hZero i f m)) atTop
      (𝓝 (∫ v : CompleteWorld Unit, (f (v.2.1 i)-∫ x, f x ∂(B.individuals i:Measure ℝ))*
        B.maximum (v.1,v.2.1) ∂B.completeWorldLaw (Measure.dirac ()))) := by
  have hRT := B.directScheduled_canonical_individual_score_limits_positive hZero hw hc i f
  have hR := hRT.1.const_mul (boundedScoreScale f)
  have hT := hRT.2.const_mul (boundedScoreScale f)
  have hM := (B.directIndividual_expectedMaximumScore_tendsto hZero i f).const_mul (boundedScoreScale f)
  rw [mul_integral_centeredBoundedScore] at hR hT
  have hMaxTarget : boundedScoreScale f*B.prophetIndividualLikelihoodDerivative i
      (centeredBoundedScore (B.individuals i:Measure ℝ) f)=
      ∫ v : CompleteWorld Unit, (f (v.2.1 i)-∫ x, f x ∂(B.individuals i:Measure ℝ))*
        B.maximum (v.1,v.2.1) ∂B.completeWorldLaw (Measure.dirac ()) := by
    unfold prophetIndividualLikelihoodDerivative
    simp_rw [mul_comm (B.maximum _)]
    exact mul_integral_centeredBoundedScore _ f _ _ _
  rw [hMaxTarget] at hM
  refine ⟨hR.congr (fun m => ?_),hT.congr (fun m => ?_),hM.congr (fun m => ?_)⟩
  · exact ((B.directCanonicalPolicy hZero hw hc m).expectedRewardScore_const_mul _ (boundedScoreScale f) _).symm
  · exact ((B.directCanonicalPolicy hZero hw hc m).expectedDurationScore_const_mul _ (boundedScoreScale f) _).symm
  · exact ((B.directFiniteApproximation hZero m).expectedMaximumScore_const_mul (boundedScoreScale f) _).symm

 theorem directScheduled_coarse_unscaled_individual_score_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (K : ℕ) (d : ℝ) (hd : (B.terminal:ℝ)<d) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (i : Fin K) (f : ℝ →ᵇ ℝ) :
    let D := B.truncation K d hd
    let π := D.valueThresholdPolicy hw.le hc.le
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedRewardScore
      (B.directFiniteApproximation hZero m) (B.directUnscaledIndividualScore hZero i.val f m)) atTop
      (𝓝 (∫ v, (f (v.2.1 i)-∫ x, f x ∂(B.individuals i.val:Measure ℝ))*
        (D.valueRule w c).realizedReward 0 v ∂D.law (Measure.dirac ()))) ∧
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedDurationScore
      (B.directFiniteApproximation hZero m) (B.directUnscaledIndividualScore hZero i.val f m)) atTop
      (𝓝 (∫ v, (f (v.2.1 i)-∫ x, f x ∂(B.individuals i.val:Measure ℝ))*
        (D.valueRule w c).realizedDuration v ∂D.law (Measure.dirac ()))) := by
  have h := B.directScheduled_coarse_individual_score_tendsto hZero K d hd hw hc i f
  have hR := h.1.const_mul (boundedScoreScale f)
  have hT := h.2.const_mul (boundedScoreScale f)
  rw [mul_integral_centeredBoundedScore] at hR hT
  constructor
  · exact hR.congr (fun m => (Model.RandomizedPolicy.expectedRewardScore_const_mul _ _ (boundedScoreScale f) _).symm)
  · exact hT.congr (fun m => (Model.RandomizedPolicy.expectedDurationScore_const_mul _ _ (boundedScoreScale f) _).symm)
end ProphetSecretary.Limiting.CountableInstance
