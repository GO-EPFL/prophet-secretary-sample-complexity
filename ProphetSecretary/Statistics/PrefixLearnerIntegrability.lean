import ProphetSecretary.Statistics.PrefixLearnerPerformance

/-!
# Integrability in the independent-array execution

Actual product-law transport gives integrability of reward and duration
before the finite-prior expectation is split into its atoms. Offer bounds
are almost sure; no boundedness on impossible raw observations is needed.
-/

open MeasureTheory Set
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Seed : Type} [MeasurableSpace Seed]

lemma integrable_prefixLearner_reward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (N b k : ℕ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) :
    Integrable (fun z : ValueArray n N × ((Fin n → ℝ) × Seed) =>
      π.reward (prefixVisibleArray n N b k z.1,z.2.2) Finset.univ
        (fun i => z.1 (i,Fin.last N)) z.2.1)
      ((P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) := by
  let L := prefixLearner N b k ν π hπ
  have hMP := prefixExecutionWorld_measurePreserving P N b k ν
  have h := hMP.integrable_comp_of_integrable ((L.randomizedPolicy P).integrable_realizedReward P hP)
  change Integrable (fun z : ValueArray n N × ((Fin n → ℝ) × Seed) =>
    (prefixLearner N b k ν π hπ).policy.reward (prefixExecutionWorld n N b k z).2.2 Finset.univ
      (prefixExecutionWorld n N b k z).1 (prefixExecutionWorld n N b k z).2.1)
    ((P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) at h
  rw [prefixLearner_policy_eq_comap] at h
  exact h

lemma integrable_prefixLearner_duration (P : Instance n) (N b k : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) :
    Integrable (fun z : ValueArray n N × ((Fin n → ℝ) × Seed) =>
      π.stoppingTime (prefixVisibleArray n N b k z.1,z.2.2) Finset.univ
        (fun i => z.1 (i,Fin.last N)) z.2.1)
      ((P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) := by
  let L := prefixLearner N b k ν π hπ
  have hMP := prefixExecutionWorld_measurePreserving P N b k ν
  have h := hMP.integrable_comp_of_integrable ((L.randomizedPolicy P).integrable_realizedDuration P)
  change Integrable (fun z : ValueArray n N × ((Fin n → ℝ) × Seed) =>
    (prefixLearner N b k ν π hπ).policy.stoppingTime (prefixExecutionWorld n N b k z).2.2 Finset.univ
      (prefixExecutionWorld n N b k z).1 (prefixExecutionWorld n N b k z).2.1)
    ((P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν)) at h
  rw [prefixLearner_policy_eq_comap] at h
  exact h

lemma onlineArray_measurePreserving (P : Instance n) (N : ℕ) :
    MeasurePreserving (fun a : ValueArray n N => fun i => a (i,Fin.last N))
      (P.trainingCoordinateLaw (N+1)) P.valuesLaw :=
  measurePreserving_snd.comp (prefixOnlineValues_measurePreserving P N 0 (Nat.zero_le N))

lemma integrable_onlineArray_maximum {Aux : Type*} [MeasurableSpace Aux]
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (N : ℕ)
    (ν : Measure Aux) [IsProbabilityMeasure ν] :
    Integrable (fun z : ValueArray n N × Aux => Instance.maximum (fun i => z.1 (i,Fin.last N)))
      ((P.trainingCoordinateLaw (N+1)).prod ν) := by
  have hMP : MeasurePreserving (fun z : ValueArray n N × Aux => fun i => z.1 (i,Fin.last N))
      ((P.trainingCoordinateLaw (N+1)).prod ν) P.valuesLaw :=
    (onlineArray_measurePreserving P N).comp measurePreserving_fst
  exact hMP.integrable_comp_of_integrable hP

lemma integral_onlineArray_maximum {Aux : Type*} [MeasurableSpace Aux]
    (P : Instance n) (N : ℕ) (ν : Measure Aux) [IsProbabilityMeasure ν] :
    (∫ z : ValueArray n N × Aux, Instance.maximum (fun i => z.1 (i,Fin.last N))
      ∂(P.trainingCoordinateLaw (N+1)).prod ν)=P.expectedMaximum := by
  have hMP : MeasurePreserving (fun z : ValueArray n N × Aux => fun i => z.1 (i,Fin.last N))
      ((P.trainingCoordinateLaw (N+1)).prod ν) P.valuesLaw :=
    (onlineArray_measurePreserving P N).comp measurePreserving_fst
  exact hMP.hasLaw.integral_comp Instance.measurable_maximum.aestronglyMeasurable

end ProphetSecretary.Statistics.FinitePrior
