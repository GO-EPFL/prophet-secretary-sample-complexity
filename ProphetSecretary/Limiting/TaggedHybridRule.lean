import ProphetSecretary.Limiting.ChronologicalHistoryTags
import ProphetSecretary.Limiting.HybridScalarObjectives
import ProphetSecretary.Probability.FiniteMeasureTotalization
import ProphetSecretary.Probability.IIDPrefix

/-!
# Count-hidden hybrid callbacks with occurrence tags

A tag is supplied with the current anonymous offer and in its strict past
measure. The callbacks receive neither the Poisson count nor construction
labels. An ordinary hybrid policy realizes these observations from one
independent infinite tag sequence indexed by the observed chronological rank.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

structure TaggedHybridRule (n : ℕ) (Seed T : Type*) [MeasurableSpace T] where
  individual : Seed → ℝ → Fin n → ℝ → Model.History n → Measure (ℝ × (ℝ × T)) → Bool
  poisson : Seed → ℝ → ℝ → T → Model.History n → Measure (ℝ × (ℝ × T)) → Bool

variable {n : ℕ} {Seed T : Type*} [MeasurableSpace T]

def TaggedHybridRule.IsMeasurable [MeasurableSpace Seed] (π : TaggedHybridRule n Seed T) : Prop :=
  Measurable (fun z : Seed × (ℝ × (Fin n × (ℝ × (Model.History n × Measure (ℝ × (ℝ × T)))))) =>
    π.individual z.1 z.2.1 z.2.2.1 z.2.2.2.1 z.2.2.2.2.1 z.2.2.2.2.2) ∧
  Measurable (fun z : Seed × ((ℝ × (ℝ × T)) × (Model.History n × Measure (ℝ × (ℝ × T)))) =>
    π.poisson z.1 z.2.1.1 z.2.1.2.1 z.2.1.2.2 z.2.2.1 z.2.2.2)

noncomputable def TaggedHybridRule.sampleTags (π : TaggedHybridRule n Seed T) : HybridRule n (Seed × (ℕ → T)) where
  individual r t i x H ξ := π.individual r.1 t i x H
    (chronologicalTaggedHistory r.2 (ProphetSecretary.Probability.finiteMeasureOrZero ξ))
  poisson r t x H ξ := π.poisson r.1 t x
    (r.2 (finitePastRank (ProphetSecretary.Probability.finiteMeasureOrZero ξ) t)) H
    (chronologicalTaggedHistory r.2 (ProphetSecretary.Probability.finiteMeasureOrZero ξ))

lemma TaggedHybridRule.sampleTags_isMeasurable [MeasurableSpace Seed]
    (π : TaggedHybridRule n Seed T) (hπ : π.IsMeasurable) : π.sampleTags.IsMeasurable := by
  have hEval : Measurable (fun z : (ℕ → T) × ℕ => z.1 z.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  have hFinite := ProphetSecretary.Probability.measurable_finiteMeasureOrZero (α := Point)
  constructor
  · let Ω := (Seed × (ℕ → T)) × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point))))
    have hPast : Measurable (fun z : Ω => chronologicalTaggedHistory z.1.2
        (ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2.2.2)) :=
      measurable_chronologicalTaggedHistory.comp (measurable_fst.snd.prodMk (hFinite.comp measurable_snd.snd.snd.snd.snd))
    exact hπ.1.comp (measurable_fst.fst.prodMk (measurable_snd.fst.prodMk
      (measurable_snd.snd.fst.prodMk (measurable_snd.snd.snd.fst.prodMk (measurable_snd.snd.snd.snd.fst.prodMk hPast)))))
  · let Ω := (Seed × (ℕ → T)) × (Point × (Model.History n × Measure Point))
    have hFinitePast : Measurable (fun z : Ω => ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2) :=
      hFinite.comp measurable_snd.snd.snd
    have hPast : Measurable (fun z : Ω => chronologicalTaggedHistory z.1.2
        (ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2)) :=
      measurable_chronologicalTaggedHistory.comp (measurable_fst.snd.prodMk hFinitePast)
    have hRank : Measurable (fun z : Ω => finitePastRank (ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2) z.2.1.1) :=
      measurable_finitePastRank.comp (hFinitePast.prodMk measurable_snd.fst.fst)
    have hTag : Measurable (fun z : Ω => z.1.2 (finitePastRank (ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2) z.2.1.1)) :=
      hEval.comp (measurable_fst.snd.prodMk hRank)
    exact hπ.2.comp (measurable_fst.fst.prodMk
      ((measurable_snd.fst.fst.prodMk (measurable_snd.fst.snd.prodMk hTag)).prodMk (measurable_snd.snd.fst.prodMk hPast)))

structure RandomizedTaggedHybridPolicy (n : ℕ) (T : Type) [MeasurableSpace T] where
  Seed : Type
  [seedSpace : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [probability : IsProbabilityMeasure seedLaw]
  rule : TaggedHybridRule n Seed T
  measurable_rule : rule.IsMeasurable

attribute [instance] RandomizedTaggedHybridPolicy.seedSpace RandomizedTaggedHybridPolicy.probability

noncomputable def RandomizedTaggedHybridPolicy.sampleTags {T : Type} [MeasurableSpace T]
    (π : RandomizedTaggedHybridPolicy n T) (κ : Measure T) [IsProbabilityMeasure κ] : RandomizedHybridPolicy n where
  Seed := π.Seed × (ℕ → T)
  seedLaw := π.seedLaw.prod (Measure.infinitePi (fun _ : ℕ => κ))
  rule := π.rule.sampleTags
  measurable_rule := π.rule.sampleTags_isMeasurable π.measurable_rule

end ProphetSecretary.Limiting
