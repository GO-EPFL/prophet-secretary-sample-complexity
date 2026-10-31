import ProphetSecretary.Statistics.PrefixLearnerWorld
import Mathlib.Probability.HasLaw

/-!
# Actual reward and duration means of a prefix-observable policy

The independent-array experiment and the implemented learner have the
same expected reward and duration. The array map first removes every
unobserved training coordinate; the separate ONLINE vector is used only
by the online execution. Integrability follows from the actual product law.
-/

open MeasureTheory Set
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Seed : Type} [MeasurableSpace Seed]

def prefixVisibleArray (n N b k : ℕ) (a : ValueArray n N) : ValueArray n N :=
  extendTrainingPrefix n N b k (reservoirCoordinates.symm
    (prefixOnlineValues n N (trainingLength N b k) (trainingLength_le N b k) a).1)

lemma integral_prefixLearner_reward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (N b k : ℕ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) :
    (∫ z : ValueArray n N × ((Fin n → ℝ) × Seed),
      π.reward (prefixVisibleArray n N b k z.1,z.2.2) Finset.univ
        (fun i => z.1 (i,Fin.last N)) z.2.1
      ∂(P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) =
      (prefixLearner N b k ν π hπ).expectedReward P := by
  let L := prefixLearner N b k ν π hπ
  have hMP := prefixExecutionWorld_measurePreserving P N b k ν
  have hInt := (L.randomizedPolicy P).integrable_realizedReward P hP
  have h := hMP.hasLaw.integral_comp hInt.aestronglyMeasurable
  change (∫ z : ValueArray n N × ((Fin n → ℝ) × Seed),
      (prefixLearner N b k ν π hπ).policy.reward (prefixExecutionWorld n N b k z).2.2 Finset.univ
        (prefixExecutionWorld n N b k z).1 (prefixExecutionWorld n N b k z).2.1
      ∂(P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) =
      (prefixLearner N b k ν π hπ).expectedReward P at h
  rw [prefixLearner_policy_eq_comap] at h
  exact h

lemma integral_prefixLearner_duration (P : Instance n) (N b k : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) :
    (∫ z : ValueArray n N × ((Fin n → ℝ) × Seed),
      π.stoppingTime (prefixVisibleArray n N b k z.1,z.2.2) Finset.univ
        (fun i => z.1 (i,Fin.last N)) z.2.1
      ∂(P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) =
      (prefixLearner N b k ν π hπ).meanDuration P := by
  let L := prefixLearner N b k ν π hπ
  have hMP := prefixExecutionWorld_measurePreserving P N b k ν
  have hInt := (L.randomizedPolicy P).integrable_realizedDuration P
  have h := hMP.hasLaw.integral_comp hInt.aestronglyMeasurable
  change (∫ z : ValueArray n N × ((Fin n → ℝ) × Seed),
      (prefixLearner N b k ν π hπ).policy.stoppingTime (prefixExecutionWorld n N b k z).2.2 Finset.univ
        (prefixExecutionWorld n N b k z).1 (prefixExecutionWorld n N b k z).2.1
      ∂(P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) =
      (prefixLearner N b k ν π hπ).meanDuration P at h
  rw [prefixLearner_policy_eq_comap] at h
  exact h

end ProphetSecretary.Statistics.FinitePrior
