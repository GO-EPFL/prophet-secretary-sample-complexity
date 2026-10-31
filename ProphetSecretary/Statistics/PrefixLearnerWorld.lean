import ProphetSecretary.Statistics.PosteriorEmpiricalLearner
import ProphetSecretary.Statistics.FinitePriorConditionalSampling

/-!
# Exact product law for a prefix learner's online execution

The unused columns are integrated out. The observed training reservoir and
the distinct ONLINE column have their actual independent product laws,
as do arrival clocks and arbitrary policy randomness. The execution map
supplies no unused training column or ONLINE value to the learner's seed.
-/

open MeasureTheory Set
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Seed : Type} [MeasurableSpace Seed]

def prefixExecutionWorld (n N b k : ℕ)
    (z : ValueArray n N × ((Fin n → ℝ) × Seed)) :
    (Fin n → ℝ) × ((Fin n → ℝ) × (Reservoir n (trainingLength N b k) × Seed)) :=
  ((prefixOnlineValues n N (trainingLength N b k) (trainingLength_le N b k) z.1).2,
    (z.2.1,(reservoirCoordinates.symm
      (prefixOnlineValues n N (trainingLength N b k) (trainingLength_le N b k) z.1).1,z.2.2)))

lemma prefixExecutionWorld_measurePreserving (P : Instance n) (N b k : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (prefixExecutionWorld n N b k)
      ((P.trainingCoordinateLaw (N+1)).prod ((Instance.clocksLaw n).prod ν))
      (P.worldLaw ((P.reservoirLaw (trainingLength N b k)).prod ν)) := by
  let c := trainingLength N b k
  have hData : MeasurePreserving (fun a : ValueArray n N =>
      ((prefixOnlineValues n N c (trainingLength_le N b k) a).2,
        reservoirCoordinates.symm (prefixOnlineValues n N c (trainingLength_le N b k) a).1))
      (P.trainingCoordinateLaw (N+1)) (P.valuesLaw.prod (P.reservoirLaw c)) :=
    ((MeasurePreserving.id P.valuesLaw).prod (P.reservoirCoordinates_symm_measurePreserving c)).comp
      ((Measure.measurePreserving_swap (μ:=P.trainingCoordinateLaw c) (ν:=P.valuesLaw)).comp
        (prefixOnlineValues_measurePreserving P N c (trainingLength_le N b k)))
  have hSwap : MeasurePreserving (fun a : Reservoir n c × ((Fin n → ℝ) × Seed) =>
      (a.2.1,(a.1,a.2.2))) ((P.reservoirLaw c).prod ((Instance.clocksLaw n).prod ν))
      ((Instance.clocksLaw n).prod ((P.reservoirLaw c).prod ν)) :=
    (measurePreserving_prodAssoc (Instance.clocksLaw n) (P.reservoirLaw c) ν).comp
      (((Measure.measurePreserving_swap (μ:=P.reservoirLaw c) (ν:=Instance.clocksLaw n)).prod
        (MeasurePreserving.id ν)).comp
        ((measurePreserving_prodAssoc (P.reservoirLaw c) (Instance.clocksLaw n) ν).symm MeasurableEquiv.prodAssoc))
  exact ((MeasurePreserving.id P.valuesLaw).prod hSwap).comp
    ((measurePreserving_prodAssoc P.valuesLaw (P.reservoirLaw c) ((Instance.clocksLaw n).prod ν)).comp
      (hData.prod (MeasurePreserving.id ((Instance.clocksLaw n).prod ν))))

omit [MeasurableSpace Seed] in
lemma prefixExecutionWorld_eq_observed (F : FinitePrior n) (N b k : ℕ) (ω : BaseWorld F N)
    (u : Fin n → ℝ) (r : Seed) :
    prefixExecutionWorld n N b k (ω.2,(u,r))=(F.onlineValues ω,(u,(F.observedTraining N b k ω,r))) := by
  rw [F.observedTraining_eq]
  rfl

lemma prefixLearner_reward_eq_observed (F : FinitePrior n) (N b k : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable)
    (ω : BaseWorld F N) (u : Fin n → ℝ) (r : Seed) :
    (prefixLearner N b k ν π hπ).policy.reward (F.observedTraining N b k ω,r) Finset.univ (F.onlineValues ω) u =
      π.reward (F.observe N b k ω,r) Finset.univ (F.onlineValues ω) u := by
  rw [prefixLearner_policy_eq_comap]
  change π.reward (extendTrainingPrefix n N b k (F.observedTraining N b k ω),r)
    Finset.univ (F.onlineValues ω) u= _
  rw [F.extend_observedTraining_eq]

lemma prefixLearner_duration_eq_observed (F : FinitePrior n) (N b k : ℕ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable)
    (ω : BaseWorld F N) (u : Fin n → ℝ) (r : Seed) :
    (prefixLearner N b k ν π hπ).policy.stoppingTime (F.observedTraining N b k ω,r) Finset.univ (F.onlineValues ω) u =
      π.stoppingTime (F.observe N b k ω,r) Finset.univ (F.onlineValues ω) u := by
  rw [prefixLearner_policy_eq_comap]
  change π.stoppingTime (extendTrainingPrefix n N b k (F.observedTraining N b k ω),r)
    Finset.univ (F.onlineValues ω) u= _
  rw [F.extend_observedTraining_eq]

end ProphetSecretary.Statistics.FinitePrior
