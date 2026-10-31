import ProphetSecretary.Model.RankLearner
import ProphetSecretary.Model.AllSamplesLearner

/-!
# Full-sample realization of rank decision rules

The full request protocol decodes its observed transcript to the sample array.
Consequently any jointly measurable sample-based rank rule is an actual
causal learner with the same per-distribution budget, on every raw outcome.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n k : ℕ}

noncomputable def RankLearner.ofSamplePolicy (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : RankPolicy (Reservoir n k × Seed) n) (hπ : π.IsMeasurable) : RankLearner n k where
  Seed := Seed
  seedLaw := ν
  request := requestAll k
  measurable_request := measurable_requestAll
  decide r D q i x H := π.decide (decodedReservoir D,r) q i x H
  measurable_decide := by
    let A := (Seed × Transcript n) × (Fin n × (Fin n × (ℝ × RankHistory n)))
    have hd : Measurable (fun z : A => decodedReservoir (k := k) z.1.2) :=
      (measurable_decodedReservoir (n := n) (k := k)).comp (measurable_snd.comp measurable_fst)
    have hr : Measurable (fun z : A => z.1.1) := measurable_fst.comp measurable_fst
    exact hπ.comp ((hd.prodMk hr).prodMk measurable_snd)

lemma RankLearner.ofSamplePolicy_decide (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : RankPolicy (Reservoir n k × Seed) n) (hπ : π.IsMeasurable)
    (y : Reservoir n k) (r : Seed) (q i : Fin n) (x : ℝ) (H : RankHistory n) :
    (RankLearner.ofSamplePolicy Seed ν π hπ).policy.decide (y,r) q i x H = π.decide (y,r) q i x H := by
  change π.decide (decodedReservoir (trainingTranscript (requestAll k) r y),r) q i x H = _
  rw [decodedReservoir_trainingTranscript]

lemma RankLearner.ofSamplePolicy_requests_eq (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : RankPolicy (Reservoir n k × Seed) n) (hπ : π.IsMeasurable)
    (y : Reservoir n k) (r : Seed) (i : Fin n) :
    requests (trainingTranscript (RankLearner.ofSamplePolicy Seed ν π hπ).request r y) i = k :=
  train_requestAll_full r y (n*k) [] (by simp [WithinBudget]) (by simp) i

noncomputable def RankLearner.fullSampling (L : RankLearner n k) : RankLearner n k :=
  RankLearner.ofSamplePolicy L.Seed L.seedLaw L.policy L.policy_isMeasurable

lemma RankLearner.fullSampling_policy (L : RankLearner n k) : L.fullSampling.policy = L.policy := by
  have h : L.fullSampling.policy.decide = L.policy.decide := by
    funext y q i x H
    exact RankLearner.ofSamplePolicy_decide L.Seed L.seedLaw L.policy L.policy_isMeasurable y.1 y.2 q i x H
  exact congrArg RankPolicy.mk h

end ProphetSecretary.Model
