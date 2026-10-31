import ProphetSecretary.Limiting.TaggedHybridRule
import ProphetSecretary.Limiting.ChronologicalConditionalHistory

/-!
# A causal ordinary hybrid rule reconstructing tagged payloads

The original callbacks see only the reconstructed current old value/tag and
reconstructed strict past. The independent uniform sequence is not supplied
to them. Retained histories are copied, including zero-valued identities.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed U T : Type*} [MeasurableSpace U] [MeasurableSpace T]

noncomputable def TaggedHybridRule.reconstructPayload (π : TaggedHybridRule n Seed T)
    (F : ℝ × U → ℝ × T) : HybridRule n (Seed × (ℕ → U)) where
  individual r t i x H ξ := π.individual r.1 t i x H
    (conditionalPayloadHistory F r.2 (ProphetSecretary.Probability.finiteMeasureOrZero ξ))
  poisson r t x H ξ :=
    let z := F (x,r.2 (finitePastRank (ProphetSecretary.Probability.finiteMeasureOrZero ξ) t))
    π.poisson r.1 t z.1 z.2 H
      (conditionalPayloadHistory F r.2 (ProphetSecretary.Probability.finiteMeasureOrZero ξ))

lemma TaggedHybridRule.reconstructPayload_isMeasurable [MeasurableSpace Seed]
    (π : TaggedHybridRule n Seed T) (hπ : π.IsMeasurable) {F : ℝ × U → ℝ × T} (hF : Measurable F) :
    (π.reconstructPayload F).IsMeasurable := by
  have hEval : Measurable (fun z : (ℕ → U) × ℕ => z.1 z.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  have hFinite := ProphetSecretary.Probability.measurable_finiteMeasureOrZero (α := Point)
  constructor
  · let Ω := (Seed × (ℕ → U)) × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point))))
    have hPast : Measurable (fun z : Ω => conditionalPayloadHistory F z.1.2
        (ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2.2.2)) :=
      (measurable_conditionalPayloadHistory hF).comp
        (measurable_fst.snd.prodMk (hFinite.comp measurable_snd.snd.snd.snd.snd))
    exact hπ.1.comp (measurable_fst.fst.prodMk (measurable_snd.fst.prodMk
      (measurable_snd.snd.fst.prodMk (measurable_snd.snd.snd.fst.prodMk (measurable_snd.snd.snd.snd.fst.prodMk hPast)))))
  · let Ω := (Seed × (ℕ → U)) × (Point × (Model.History n × Measure Point))
    have hFinitePast : Measurable (fun z : Ω => ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2) :=
      hFinite.comp measurable_snd.snd.snd
    have hPast : Measurable (fun z : Ω => conditionalPayloadHistory F z.1.2
        (ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2)) :=
      (measurable_conditionalPayloadHistory hF).comp (measurable_fst.snd.prodMk hFinitePast)
    have hRank : Measurable (fun z : Ω => finitePastRank (ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2) z.2.1.1) :=
      measurable_finitePastRank.comp (hFinitePast.prodMk measurable_snd.fst.fst)
    have hCurrent : Measurable (fun z : Ω => F (z.2.1.2,
        z.1.2 (finitePastRank (ProphetSecretary.Probability.finiteMeasureOrZero z.2.2.2) z.2.1.1))) :=
      hF.comp (measurable_snd.fst.snd.prodMk (hEval.comp (measurable_fst.snd.prodMk hRank)))
    exact hπ.2.comp (measurable_fst.fst.prodMk
      ((measurable_snd.fst.fst.prodMk hCurrent).prodMk (measurable_snd.snd.fst.prodMk hPast)))

noncomputable def RandomizedTaggedHybridPolicy.reconstructPolicy {n : ℕ} {U T : Type}
    [MeasurableSpace U] [MeasurableSpace T] (π : RandomizedTaggedHybridPolicy n T)
    (ρ : Measure U) [IsProbabilityMeasure ρ] (F : ℝ × U → ℝ × T) (hF : Measurable F) : RandomizedHybridPolicy n where
  Seed := π.Seed × (ℕ → U)
  seedLaw := π.seedLaw.prod (Measure.infinitePi (fun _ : ℕ => ρ))
  rule := π.rule.reconstructPayload F
  measurable_rule := π.rule.reconstructPayload_isMeasurable π.measurable_rule hF

end ProphetSecretary.Limiting
