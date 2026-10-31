import ProphetSecretary.Model.RankLearner
import ProphetSecretary.Model.RankToClockLaw

/-!
# Exact adaptive rank-learner transport to clocks

The seed law and adaptive request rule are unchanged. The observed training
transcript is supplied to a rank policy, whose online history is recovered
causally from clock observations. Thus the transcript and hard budget agree on
every training outcome, and actual reward and reach guarantees transfer.
-/

open MeasureTheory
namespace ProphetSecretary.Model
namespace RankLearner
variable {n k : ℕ} (L : RankLearner n k)

def transcriptRankPolicy : RankPolicy (L.Seed × Transcript n) n where
  decide z rank i x H := L.decide z.1 z.2 rank i x H

lemma transcriptRankPolicy_measurable : L.transcriptRankPolicy.IsMeasurable := L.measurable_decide

noncomputable def rankToClock : Learner n k where
  Seed := L.Seed
  seedLaw := L.seedLaw
  request := L.request
  measurable_request := L.measurable_request
  decide r T t i x H := L.transcriptRankPolicy.rankToClock.decide (r,T) t i x H
  measurable_decide := L.transcriptRankPolicy.rankToClock_measurable L.transcriptRankPolicy_measurable

lemma rankToClock_request (r : L.Seed) (T : Transcript n) : L.rankToClock.request r T=L.request r T := rfl

lemma rankToClock_transcript (r : L.Seed) (y : Reservoir n k) :
    trainingTranscript L.rankToClock.request r y=trainingTranscript L.request r y := rfl

lemma rankToClock_hard_budget (r : L.Seed) (y : Reservoir n k) (i : Fin n) :
    requests (trainingTranscript L.rankToClock.request r y) i≤k := L.hard_budget r y i

lemma rankToClock_policy : L.rankToClock.policy=L.policy.rankToClock := rfl

lemma rankToClock_randomizedPolicy (P : Instance n) :
    L.rankToClock.randomizedPolicy P=(L.randomizedPolicy P).rankToClock := rfl

lemma rankToClock_expectedReward (P : Instance n) : L.rankToClock.expectedReward P=L.expectedReward P := by
  change (L.rankToClock.randomizedPolicy P).expectedReward P=(L.randomizedPolicy P).expectedReward P
  rw [L.rankToClock_randomizedPolicy P]
  exact (L.randomizedPolicy P).rankToClock_expectedReward P

lemma rankToClock_reachProbability (P : Instance n) (i : Fin n) :
    L.rankToClock.reachProbability P i=L.reachProbability P i := by
  change L.rankToClock.policy.reachProbability P ((P.reservoirLaw k).prod L.seedLaw) i=
    (L.randomizedPolicy P).reachProbability P i
  rw [L.rankToClock_policy]
  exact (L.randomizedPolicy P).rankToClock_reach_probability P i

lemma rankToClock_guarantees_iff (rho : ℝ) : L.rankToClock.Guarantees rho ↔ L.Guarantees rho := by
  constructor
  · intro h P hP
    rw [←L.rankToClock_expectedReward P]
    exact h P hP
  · intro h P hP
    rw [L.rankToClock_expectedReward P]
    exact h P hP

end RankLearner
end ProphetSecretary.Model
