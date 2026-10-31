import ProphetSecretary.Statistics.RankLearnerTableLaw
import ProphetSecretary.Probability.FiniteSimplexLaw
import ProphetSecretary.Statistics.FiniteResponseGame
import ProphetSecretary.Model.RankLearnerToClock

/-!
# The reward-or-reach target game in rank observations

The hidden target is reward or one specified identity's reach. The benchmark
is respectively the expected maximum or one. The same game is preserved by
the causal rank-to-clock construction and by the finite-table representation.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model
variable {n k : ℕ}

noncomputable def RankLearner.targetGamePayoff (L : RankLearner n k) (P : Instance n)
    (J : Option (Fin n)) (C : ℝ) : ℝ :=
  match J with
  | none => L.expectedReward P-C*P.expectedMaximum
  | some i => L.reachProbability P i-C

lemma RankLearner.rankToClock_targetGamePayoff (L : RankLearner n k) (P : Instance n)
    (J : Option (Fin n)) (C : ℝ) : L.rankToClock.targetGamePayoff P J C=L.targetGamePayoff P J C := by
  cases J <;> simp only [Learner.targetGamePayoff,RankLearner.targetGamePayoff,
    L.rankToClock_expectedReward,L.rankToClock_reachProbability]

end ProphetSecretary.Model

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability
variable {n k : ℕ}

lemma mixedRankTableLearner_targetGamePayoff (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (G : Finset ℝ) (ν : Measure (RankStrategyTable n k G)) [IsProbabilityMeasure ν]
    (J : Option (Fin n)) (C : ℝ) :
    (mixedRankTableLearner G ν).targetGamePayoff P J C =
      ∑ T, ν.real {T}*(finiteRankTableLearner G T).targetGamePayoff P J C := by
  have hMass := (finiteProbability_singletons_simplex ν).2
  cases J with
  | none =>
    simp only [RankLearner.targetGamePayoff]
    rw [mixedRankTableLearner_expectedReward P hP G ν]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hMass,one_mul]
  | some i =>
    simp only [RankLearner.targetGamePayoff]
    rw [mixedRankTableLearner_reachProbability P G ν i]
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hMass,one_mul]

lemma rankLearnerTableMixture_targetGamePayoff (L : RankLearner n k) (G : Finset ℝ)
    (hCap : ∀ y r q i H, L.policy.decide (y,r) q i 1 H = true)
    (hZero : ∀ y r q i H, L.policy.decide (y,r) q i 0 H = false)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (hG : ∀ i, ∀ᵐ x ∂P.law i, x∈G) (J : Option (Fin n)) (C : ℝ) :
    (rankLearnerTableMixture L G).targetGamePayoff P J C=L.targetGamePayoff P J C := by
  cases J <;> simp only [RankLearner.targetGamePayoff,
    rankLearnerTableMixture_expectedReward L G hCap hZero P hP hG,
    rankLearnerTableMixture_reachProbability L G hCap hZero P hG]

end ProphetSecretary.Statistics
