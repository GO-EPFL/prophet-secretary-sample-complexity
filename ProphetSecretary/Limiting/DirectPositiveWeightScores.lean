import ProphetSecretary.Limiting.DirectScheduledMeasurableBandCanonical
import ProphetSecretary.Limiting.DirectScheduledIndividualScores
import ProphetSecretary.Limiting.CountableWeightNormalization
import ProphetSecretary.Model.CanonicalWeightNormalization

/-!
# Canonical covariance convergence for arbitrary positive scalar weights

Dividing both scalar weights by their sum is an exact callback identity in
both finite and countable models. Hence normalized-weight comparison bounds
apply without changing any realized reward, duration or complete score.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

 theorem directScheduled_canonical_individual_score_limits_positive
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (i : ℕ) (f : ℝ →ᵇ ℝ) :
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedRewardScore (B.directFiniteApproximation hZero m)
      (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f)) atTop
      (𝓝 (∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*
        (B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore (B.directFiniteApproximation hZero m)
      (directIndividualScore (B.individualPrefix m) (B.directVirtualOfferInstance hZero m) i f)) atTop
      (𝓝 (∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i:Measure ℝ) f (v.2.1 i)*
        (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  have hs := add_pos hw hc
  have hwN := div_pos hw hs
  have hcN := div_pos hc hs
  have hSum : w/(w+c)+c/(w+c)=1 := by rw [← add_div,div_self hs.ne']
  have h := B.directScheduled_canonical_individual_score_limits hZero hwN hcN hSum i f
  have hπ (m) : B.directCanonicalPolicy hZero hw hc m=B.directCanonicalPolicy hZero hwN hcN m :=
    (B.directFiniteApproximation hZero m).valuePolicy_weightNormalized _ hw hc.le
  simp_rw [← hπ,← B.valueRule_weightNormalized hw hc.le] at h
  exact h

 theorem directScheduled_canonical_measurableBand_score_limits_positive
    (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedRewardScore (B.directFiniteApproximation hZero m)
      (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 (∫ v, B.bandScore S v*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))) ∧
    Tendsto (fun m => (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore (B.directFiniteApproximation hZero m)
      (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 (∫ v, B.bandScore S v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))) := by
  have hs := add_pos hw hc
  have hwN := div_pos hw hs
  have hcN := div_pos hc hs
  have hSum : w/(w+c)+c/(w+c)=1 := by rw [← add_div,div_self hs.ne']
  have h := B.directScheduled_canonical_measurableBand_score_limits hZero hS hb hSub hwN hcN hSum
  change Tendsto (fun m => (B.directCanonicalPolicy hZero hwN hcN m).expectedRewardScore _ _) _ _ ∧
    Tendsto (fun m => (B.directCanonicalPolicy hZero hwN hcN m).expectedDurationScore _ _) _ _ at h
  have hπ (m) : B.directCanonicalPolicy hZero hw hc m=B.directCanonicalPolicy hZero hwN hcN m :=
    (B.directFiniteApproximation hZero m).valuePolicy_weightNormalized _ hw hc.le
  simp_rw [← hπ,← B.valueRule_weightNormalized hw hc.le] at h
  exact h
end ProphetSecretary.Limiting.CountableInstance
