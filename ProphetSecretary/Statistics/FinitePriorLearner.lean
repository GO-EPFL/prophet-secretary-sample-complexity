import ProphetSecretary.Statistics.FinitePriorPrefixSampling

/-!
# Implementing prefix-observable policies by actual sampling

The masked observation can be reconstructed from exactly its visible training
reservoir. Every measurable online policy using that observation and an
independent seed is therefore an actual causal learner with the stated hard
budget, on every training outcome. No online column is queried in this process.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ} {Seed : Type} [MeasurableSpace Seed]

def extendTrainingPrefix (n N b k : ℕ) (y : Reservoir n (trainingLength N b k)) : ValueArray n N :=
  fun q => if h : q.2.val<trainingLength N b k then y q.1 ⟨q.2.val,h⟩ else 0

lemma measurable_extendTrainingPrefix (n N b k : ℕ) : Measurable (extendTrainingPrefix n N b k) := by
  apply measurable_pi_lambda
  intro q
  by_cases h : q.2.val<trainingLength N b k
  · simpa only [extendTrainingPrefix,dif_pos h,Function.comp_def] using
      (measurable_pi_apply (⟨q.2.val,h⟩ : Fin (trainingLength N b k))).comp (measurable_pi_apply q.1)
  · simpa only [extendTrainingPrefix,dif_neg h] using (measurable_const : Measurable (fun _ : Reservoir n (trainingLength N b k) => (0:ℝ)))

lemma extend_observedTraining_eq (F : FinitePrior n) (N b k : ℕ) (ω : BaseWorld F N) :
    extendTrainingPrefix n N b k (F.observedTraining N b k ω)=F.observe N b k ω := by
  funext q
  rcases q with ⟨i,r⟩
  by_cases h : r.val<trainingLength N b k
  · have hm : (i,r)∈trainingCoordinates n N b k := by
      simpa only [trainingCoordinates,Finset.mem_filter,Finset.mem_univ,true_and,trainingLength] using h
    rw [F.observedTraining_eq]
    simp only [extendTrainingPrefix,dif_pos h,observe,ProphetSecretary.Probability.maskCoordinates,if_pos hm]
    congr 1
  · have hm : (i,r)∉trainingCoordinates n N b k := by
      simpa only [trainingCoordinates,Finset.mem_filter,Finset.mem_univ,true_and,trainingLength] using h
    simp only [extendTrainingPrefix,dif_neg h,observe,ProphetSecretary.Probability.maskCoordinates,if_neg hm]

noncomputable def prefixSamplePolicy (N b k : ℕ) (π : Policy (ValueArray n N × Seed) n) :
    Policy (Reservoir n (trainingLength N b k) × Seed) n where
  decide p t i x h := π.decide (extendTrainingPrefix n N b k p.1,p.2) t i x h

lemma prefixSamplePolicy_isMeasurable (N b k : ℕ) {π : Policy (ValueArray n N × Seed) n}
    (hπ : π.IsMeasurable) : (prefixSamplePolicy N b k π).IsMeasurable := by
  exact hπ.comp ((((measurable_extendTrainingPrefix n N b k).comp
    (measurable_fst.comp measurable_fst)).prodMk (measurable_snd.comp measurable_fst)).prodMk measurable_snd)

noncomputable def prefixLearner (N b k : ℕ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable) : Learner n (trainingLength N b k) :=
  Learner.ofSamplePolicy Seed ν (prefixSamplePolicy N b k π) (prefixSamplePolicy_isMeasurable N b k hπ)

/-- Agreement holds at every online history, not merely in expectation. -/
lemma prefixLearner_decide (F : FinitePrior n) (N b k : ℕ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable)
    (ω : BaseWorld F N) (r : Seed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (prefixLearner N b k ν π hπ).policy.decide (F.observedTraining N b k ω,r) t i x H=
      π.decide (F.observe N b k ω,r) t i x H := by
  change (Learner.ofSamplePolicy Seed ν (prefixSamplePolicy N b k π)
    (prefixSamplePolicy_isMeasurable N b k hπ)).policy.decide (F.observedTraining N b k ω,r) t i x H=_
  rw [Learner.ofSamplePolicy_decide]
  change π.decide (extendTrainingPrefix n N b k (F.observedTraining N b k ω),r) t i x H=_
  rw [F.extend_observedTraining_eq]

lemma prefixLearner_hardBudget (N b k : ℕ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable)
    (y : Reservoir n (trainingLength N b k)) (r : Seed) (i : Fin n) :
    requests (trainingTranscript (prefixLearner N b k ν π hπ).request r y) i≤trainingLength N b k :=
  (prefixLearner N b k ν π hπ).hard_budget r y i

/-- The hypothetical swap cannot change the actual protocol or its transcript. -/
lemma prefixLearner_transcript_swap (F : FinitePrior n) (N b k : ℕ) (hk : b+k<N)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (π : Policy (ValueArray n N × Seed) n) (hπ : π.IsMeasurable)
    (ω : BaseWorld F N) (r : Seed) :
    trainingTranscript (prefixLearner N b k ν π hπ).request r
      (F.observedTraining N b k (F.swapBaseEquiv N (nextColumn N b k hk) ω))=
    trainingTranscript (prefixLearner N b k ν π hπ).request r (F.observedTraining N b k ω) :=
  by rw [F.observedTraining_swap_next]

end ProphetSecretary.Statistics.FinitePrior
