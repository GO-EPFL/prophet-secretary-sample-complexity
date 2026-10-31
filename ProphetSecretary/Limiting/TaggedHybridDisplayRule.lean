import ProphetSecretary.Limiting.TaggedHybridRule
import ProphetSecretary.Limiting.PoissonPayloadDisplay

/-!
# Forward observation of a displayed anonymous payload

An ordinary displayed-law policy is run on the current displayed value and
the displayed strict-past measure. Retained observations are unchanged. This
produces a legitimate count-hidden tagged rule with no future information.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed T : Type*} [MeasurableSpace T]

noncomputable def HybridRule.observePayload (π : HybridRule n Seed) (g : ℝ × T → ℝ) : TaggedHybridRule n Seed T where
  individual r t i x H ξ := π.individual r t i x H (ξ.map (displayPayloadPoint g))
  poisson r t x s H ξ := π.poisson r t (g (x,s)) H (ξ.map (displayPayloadPoint g))

lemma HybridRule.observePayload_isMeasurable [MeasurableSpace Seed] (π : HybridRule n Seed)
    (hπ : π.IsMeasurable) {g : ℝ × T → ℝ} (hg : Measurable g) : (π.observePayload g).IsMeasurable := by
  have hMap := Measure.measurable_map _ (measurable_displayPayloadPoint hg)
  constructor
  · exact hπ.1.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk
      (measurable_snd.snd.fst.prodMk (measurable_snd.snd.snd.fst.prodMk
        (measurable_snd.snd.snd.snd.fst.prodMk (hMap.comp measurable_snd.snd.snd.snd.snd))))))
  · exact hπ.2.comp (measurable_fst.prodMk
      ((measurable_snd.fst.fst.prodMk (hg.comp measurable_snd.fst.snd)).prodMk
        (measurable_snd.snd.fst.prodMk (hMap.comp measurable_snd.snd.snd))))

noncomputable def RandomizedHybridPolicy.observePayload {n : ℕ} {T : Type} [MeasurableSpace T]
    (π : RandomizedHybridPolicy n) (g : ℝ × T → ℝ) (hg : Measurable g) : RandomizedTaggedHybridPolicy n T where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.observePayload g
  measurable_rule := π.rule.observePayload_isMeasurable π.measurable_rule hg

end ProphetSecretary.Limiting
