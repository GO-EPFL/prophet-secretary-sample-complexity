import ProphetSecretary.Model.AllSamplesLearner

/-!
# Completing adaptive training to full sampling

An adaptive learner can be simulated by a learner that requests all k samples of
each distribution. The latter reconstructs the array from its observed transcript
and executes the original adaptive rule internally. Its online decisions agree
on every sample and seed outcome. This justifies conditioning on the full array
in statistical lower-bound arguments without giving new information to the
simulated policy or changing the hard budget.
-/

open MeasureTheory

namespace ProphetSecretary.Model.Learner

variable {n k : ℕ}

noncomputable def fullSampling (L : Learner n k) : Learner n k :=
  Learner.ofSamplePolicy L.Seed L.seedLaw L.policy L.policy_isMeasurable

theorem fullSampling_decide (L : Learner n k) (y : Reservoir n k) (r : L.Seed)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    L.fullSampling.policy.decide (y, r) t i x H = L.policy.decide (y, r) t i x H :=
  Learner.ofSamplePolicy_decide L.Seed L.seedLaw L.policy L.policy_isMeasurable y r t i x H

theorem fullSampling_policy (L : Learner n k) : L.fullSampling.policy = L.policy := by
  have hdecide : L.fullSampling.policy.decide = L.policy.decide := by
    funext y t i x H
    exact L.fullSampling_decide y.1 y.2 t i x H
  exact congrArg Policy.mk hdecide

theorem fullSampling_budget (L : Learner n k) (y : Reservoir n k) (r : L.Seed) (i : Fin n) :
    requests (trainingTranscript L.fullSampling.request r y) i ≤ k :=
  L.fullSampling.hard_budget r y i

theorem fullSampling_decodedTranscript (L : Learner n k) (y : Reservoir n k) (r : L.Seed) :
    decodedReservoir (trainingTranscript L.fullSampling.request r y) = y :=
  decodedReservoir_trainingTranscript r y

theorem fullSampling_expectedReward (L : Learner n k) (P : Instance n) :
    L.fullSampling.expectedReward P = L.expectedReward P := by
  change (∫ ω : World n (Reservoir n k × L.Seed),
    L.fullSampling.policy.reward ω.2.2 Finset.univ ω.1 ω.2.1
      ∂P.worldLaw ((P.reservoirLaw k).prod L.seedLaw)) =
    ∫ ω : World n (Reservoir n k × L.Seed), L.policy.reward ω.2.2 Finset.univ ω.1 ω.2.1
      ∂P.worldLaw ((P.reservoirLaw k).prod L.seedLaw)
  rw [L.fullSampling_policy]
  rfl

theorem fullSampling_reachProbability (L : Learner n k) (P : Instance n) (i : Fin n) :
    L.fullSampling.reachProbability P i = L.reachProbability P i := by
  change L.fullSampling.policy.reachProbability P ((P.reservoirLaw k).prod L.seedLaw) i = _
  rw [L.fullSampling_policy]
  rfl

theorem fullSampling_meanDuration (L : Learner n k) (P : Instance n) :
    L.fullSampling.meanDuration P = L.meanDuration P := by
  change L.fullSampling.policy.meanDuration P ((P.reservoirLaw k).prod L.seedLaw) = _
  rw [L.fullSampling_policy]
  rfl

end ProphetSecretary.Model.Learner
