import ProphetSecretary.Model.RankLearnerToClock

/-! # Basic reward and reach bounds for general randomized rank learners -/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n k : ℕ}

lemma RankLearner.expectedReward_nonnegative (L : RankLearner n k) (P : Instance n) : 0 ≤ L.expectedReward P := by
  rw [← L.rankToClock_expectedReward P]
  exact (L.rankToClock.randomizedPolicy P).expectedReward_nonnegative P

lemma RankLearner.expectedReward_le_maximum (L : RankLearner n k) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) : L.expectedReward P ≤ P.expectedMaximum := by
  rw [← L.rankToClock_expectedReward P]
  exact (L.rankToClock.randomizedPolicy P).expectedReward_le_maximum P hP

lemma RankLearner.reachProbability_nonnegative (L : RankLearner n k) (P : Instance n) (i : Fin n) :
    0 ≤ L.reachProbability P i := ENNReal.toReal_nonneg

lemma RankLearner.reachProbability_le_one (L : RankLearner n k) (P : Instance n) (i : Fin n) :
    L.reachProbability P i ≤ 1 := by
  change ((L.randomizedPolicy P).worldLaw P).real {ω | L.policy.Reaches ω.2.2 ω.2.1 ω.1 i} ≤ 1
  exact (measureReal_mono (Set.subset_univ _)).trans_eq probReal_univ

end ProphetSecretary.Model
