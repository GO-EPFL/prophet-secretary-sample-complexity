import ProphetSecretary.Statistics.PosteriorEmpiricalBlockIndex
import ProphetSecretary.Statistics.NormalizedEmpiricalTrainingBlockRegret
import ProphetSecretary.Model.SmallMeanClamp

/-!
# Regret of the implemented observable-posterior empirical learner

The empirical block lies inside the queried prefix. The target is computed
from that same visible prefix and may be correlated with the empirical
samples. Actual block/remainder product transport proves the selected-weight
estimate; neither selector independence nor hidden-target access is assumed.
Paper correspondence: `eq:bayes-empirical-loss`.
-/

open MeasureTheory Set Filter
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n m N : ℕ} [NeZero m]

lemma posteriorEmpirical_frozen_scalar_eq_block (F : FinitePrior n) (N b k : ℕ)
    (h : b+2*m≤trainingLength N b k) (ρ : ℝ → ℝ) (hρ : Measurable ρ)
    (P : Instance n) (y : Reservoir n (trainingLength N b k)) (r : Unit) (w c : ℝ) :
    ((F.posteriorEmpiricalLearner N b k
      (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))) ρ hρ).frozenRandomizedPolicy y r).scalarObjective P w c =
    ((Learner.empiricalTrainingBlock (Measure.dirac ())
      (empiricalBlockColumn b m (trainingLength N b k) h) (F.prefixPosteriorScalar N b k ρ)
      (F.measurable_prefixPosteriorScalar N b k hρ)).frozenRandomizedPolicy y r).scalarObjective P w c := by
  let eA := empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))
  let eB := empiricalBlockColumn b m (trainingLength N b k) h
  let A := F.posteriorEmpiricalLearner N b k eA ρ hρ
  let B := Learner.empiricalTrainingBlock (Measure.dirac ()) eB (F.prefixPosteriorScalar N b k ρ)
    (F.measurable_prefixPosteriorScalar N b k hρ)
  have hRule : A.frozenRule y r=B.frozenRule y r := by
    apply congrArg Policy.mk
    funext u t i x H
    change (Learner.ofSamplePolicy Unit (Measure.dirac ())
      (prefixSamplePolicy N b k (F.posteriorEmpiricalPolicy N b k eA ρ))
      (prefixSamplePolicy_isMeasurable N b k (F.posteriorEmpiricalPolicy_isMeasurable N b k eA hρ))).policy.decide
        (y,r) t i x H =
      (Learner.ofSamplePolicy Unit (Measure.dirac ())
        (empiricalTrainingBlockPolicy eB (F.prefixPosteriorScalar N b k ρ))
        (empiricalTrainingBlockPolicy_isMeasurable eB (F.measurable_prefixPosteriorScalar N b k hρ))).policy.decide
          (y,r) t i x H
    rw [Learner.ofSamplePolicy_decide,Learner.ofSamplePolicy_decide]
    rw [F.posteriorEmpirical_samplePolicy_eq_block N b k h ρ]
  change (∫ ω : World n Unit, w*(A.frozenRule y r).reward ω.2.2 Finset.univ ω.1 ω.2.1+
    c*(A.frozenRule y r).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ())) =
    (∫ ω : World n Unit, w*(B.frozenRule y r).reward ω.2.2 Finset.univ ω.1 ω.2.1+
      c*(B.frozenRule y r).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()))
  rw [hRule]

theorem posteriorEmpirical_expected_regret_le (F : FinitePrior n) (N b k : ℕ)
    (h : b+2*m≤trainingLength N b k) {ρ : ℝ → ℝ} (hρ : Measurable ρ) {hi : ℝ}
    (hhi : hi<1) (hRange : ∀ t∈Icc (0 : ℝ) 1, ρ t∈Icc (4/5 : ℝ) hi)
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80) :
    (∫ p : Reservoir n (trainingLength N b k) × Unit,
      ((F.posteriorEmpiricalLearner N b k
        (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))) ρ hρ).frozenRandomizedPolicy p.1 p.2).normalizedRegret P
        (ρ (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1)))
      ∂(P.reservoirLaw (trainingLength N b k)).prod (Measure.dirac ())) ≤
      empiricalCapRegretConstant (1-hi)*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ) := by
  let e := empiricalBlockColumn b m (trainingLength N b k) h
  let Z := F.prefixPosteriorScalar N b k ρ
  have hZ := F.measurable_prefixPosteriorScalar N b k hρ
  have hlo : 0<1-hi := sub_pos.mpr hhi
  have hlohi : 1-hi≤(1/4 : ℝ) := by
    have h0 := hRange 0 (by norm_num : (0 : ℝ)∈Icc 0 1)
    linarith only [h0.1,h0.2]
  have hZrange (p : Reservoir n (trainingLength N b k) × Unit) : Z p∈Icc (1-hi) (1/4 : ℝ) :=
    F.posteriorEmpiricalScalar_mem N b k hhi hRange (extendTrainingPrefix n N b k p.1)
  have hBound := Learner.empiricalTrainingBlock_normalized_expected_regret_le (Measure.dirac ())
    e Z hZ hlo hlohi hZrange P hcap hM
  have hPositive (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : 0<ρ t :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ)<4/5) (hRange t ht).1
  apply le_trans _ hBound
  apply le_of_eq
  apply integral_congr_ae
  filter_upwards [] with p
  unfold RandomizedPolicy.normalizedRegret
  rw [F.posteriorEmpirical_frozen_scalar_eq_block N b k h ρ hρ P p.1 p.2]
  have hn := F.posteriorEmpiricalScalar_normalize N b k hPositive (extendTrainingPrefix n N b k p.1)
  change _ = optimalScalarValue P (1/(1+F.posteriorEmpiricalScalar N b k ρ (extendTrainingPrefix n N b k p.1)))
    (F.posteriorEmpiricalScalar N b k ρ (extendTrainingPrefix n N b k p.1)/
      (1+F.posteriorEmpiricalScalar N b k ρ (extendTrainingPrefix n N b k p.1)))-
    ((Learner.empiricalTrainingBlock (Measure.dirac ()) e Z hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P
      (1/(1+F.posteriorEmpiricalScalar N b k ρ (extendTrainingPrefix n N b k p.1)))
      (F.posteriorEmpiricalScalar N b k ρ (extendTrainingPrefix n N b k p.1)/
        (1+F.posteriorEmpiricalScalar N b k ρ (extendTrainingPrefix n N b k p.1)))
  rw [hn.1,hn.2]

end ProphetSecretary.Statistics.FinitePrior
