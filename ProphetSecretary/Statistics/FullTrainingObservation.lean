import ProphetSecretary.Model.FullSamplingReduction
import ProphetSecretary.Probability.LikelihoodInformation

/-!
# Full training observations and statistical information

Completing adaptive training to full sampling makes the independent sample array
and auxiliary seed recoverable from the observed transcript. Data processing in
both directions proves exact equality of their KL divergences. Conditioning on
the full array in `thm:bayes` therefore uses information already covered by its
training-information premise.
-/

open MeasureTheory InformationTheory

namespace ProphetSecretary.Model.Learner

variable {n k : ℕ}

def fullTrainingDecoder (L : Learner n k) (d : L.Seed × Transcript n) : Reservoir n k × L.Seed :=
  (decodedReservoir d.2, d.1)

lemma measurable_fullTrainingDecoder (L : Learner n k) : Measurable L.fullTrainingDecoder :=
  ((measurable_decodedReservoir (n := n) (k := k)).comp measurable_snd).prodMk measurable_fst

theorem fullTrainingDecoder_measurePreserving (L : Learner n k) (P : Instance n) :
    MeasurePreserving L.fullTrainingDecoder (L.fullSampling.transcriptLaw P)
      ((P.reservoirLaw k).prod L.seedLaw) := by
  refine ⟨L.measurable_fullTrainingDecoder, ?_⟩
  change (((P.reservoirLaw k).prod L.seedLaw).map (fun z : Reservoir n k × L.Seed =>
    (z.2, trainingTranscript (requestAll k) z.2 z.1))).map L.fullTrainingDecoder = _
  have hobs : Measurable (fun z : Reservoir n k × L.Seed =>
      (z.2, trainingTranscript (requestAll k) z.2 z.1)) :=
    measurable_snd.prodMk (measurable_trainingTranscript (requestAll k) measurable_requestAll
      measurable_snd measurable_fst)
  rw [Measure.map_map L.measurable_fullTrainingDecoder hobs]
  have heq : (L.fullTrainingDecoder ∘ fun z : Reservoir n k × L.Seed =>
      (z.2, trainingTranscript (requestAll k) z.2 z.1)) = id := by
    funext z
    change (decodedReservoir (trainingTranscript (requestAll k) z.2 z.1), z.2) = z
    rw [decodedReservoir_trainingTranscript]
  rw [heq, Measure.map_id]

/-- The full transcript and the independently drawn full reservoir contain exactly
the same statistical information, including the learner's auxiliary randomness. -/
theorem fullTraining_klDiv_eq (L : Learner n k) (P Q : Instance n) :
    klDiv (L.fullSampling.transcriptLaw P) (L.fullSampling.transcriptLaw Q) =
      klDiv ((P.reservoirLaw k).prod L.seedLaw) ((Q.reservoirLaw k).prod L.seedLaw) := by
  let obs : Reservoir n k × L.Seed → L.Seed × Transcript n := fun z =>
    (z.2, trainingTranscript (requestAll k) z.2 z.1)
  have hobs : Measurable obs :=
    measurable_snd.prodMk (measurable_trainingTranscript (requestAll k) measurable_requestAll
      measurable_snd measurable_fst)
  have hForward := ProphetSecretary.Probability.klDiv_map_le ((P.reservoirLaw k).prod L.seedLaw)
    ((Q.reservoirLaw k).prod L.seedLaw) obs hobs
  letI : IsProbabilityMeasure (((P.reservoirLaw k).prod L.seedLaw).map obs) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  letI : IsProbabilityMeasure (((Q.reservoirLaw k).prod L.seedLaw).map obs) :=
    Measure.isProbabilityMeasure_map hobs.aemeasurable
  have hBackward := ProphetSecretary.Probability.klDiv_map_le (((P.reservoirLaw k).prod L.seedLaw).map obs)
    (((Q.reservoirLaw k).prod L.seedLaw).map obs) L.fullTrainingDecoder L.measurable_fullTrainingDecoder
  have hP := (L.fullTrainingDecoder_measurePreserving P).map_eq
  have hQ := (L.fullTrainingDecoder_measurePreserving Q).map_eq
  change (((P.reservoirLaw k).prod L.seedLaw).map obs).map L.fullTrainingDecoder = _ at hP
  change (((Q.reservoirLaw k).prod L.seedLaw).map obs).map L.fullTrainingDecoder = _ at hQ
  rw [hP, hQ] at hBackward
  exact le_antisymm hForward hBackward

end ProphetSecretary.Model.Learner
