import ProphetSecretary.Statistics.RankTargetGame
import ProphetSecretary.Model.RankLearnerBounds

/-!
# The actual payoff and benchmark for each finite-game target

A reward target has payoff ER and benchmark M; a reach target has payoff q_i
and benchmark one. These are distinct from the instance optimal stopping value.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model
variable {n k : ℕ}

noncomputable def targetBenchmark (P : Instance n) (J : Option (Fin n)) : ℝ :=
  match J with | none => P.expectedMaximum | some _ => 1

noncomputable def RankLearner.targetPayoff (L : RankLearner n k) (P : Instance n) (J : Option (Fin n)) : ℝ :=
  match J with | none => L.expectedReward P | some i => L.reachProbability P i

lemma targetBenchmark_nonnegative (P : Instance n) (J : Option (Fin n)) : 0 ≤ targetBenchmark P J := by
  cases J
  · exact P.expectedMaximum_nonnegative
  · exact zero_le_one

lemma RankLearner.targetPayoff_nonnegative (L : RankLearner n k) (P : Instance n) (J : Option (Fin n)) :
    0 ≤ L.targetPayoff P J := by
  cases J
  · exact L.expectedReward_nonnegative P
  · exact L.reachProbability_nonnegative P _

lemma RankLearner.targetGamePayoff_eq (L : RankLearner n k) (P : Instance n) (J : Option (Fin n)) (C : ℝ) :
    L.targetGamePayoff P J C=L.targetPayoff P J-C*targetBenchmark P J := by
  cases J <;> simp only [targetGamePayoff,targetPayoff,targetBenchmark,mul_one]

end ProphetSecretary.Model

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n k : ℕ}

lemma mixedRankTableLearner_targetPayoff (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (G : Finset ℝ) (ν : Measure (RankStrategyTable n k G)) [IsProbabilityMeasure ν] (J : Option (Fin n)) :
    (mixedRankTableLearner G ν).targetPayoff P J =
      ∑ T, ν.real {T}*(finiteRankTableLearner G T).targetPayoff P J := by
  have h := mixedRankTableLearner_targetGamePayoff P hP G ν J 0
  simpa only [RankLearner.targetGamePayoff_eq,zero_mul,sub_zero] using h

end ProphetSecretary.Statistics
