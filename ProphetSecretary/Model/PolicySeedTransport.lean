import ProphetSecretary.Reach.FiniteReach
import ProphetSecretary.Model.ScalarObjectives
import Mathlib.Probability.HasLaw

/-!
# Transporting an independent policy seed

A measurable seed map changes no online observation. A measure-preserving map
therefore preserves expected reward and every reach probability.
-/

open MeasureTheory
namespace ProphetSecretary.Model
variable {n : ℕ} {A B : Type*}

def Policy.pullbackSeed (π : Policy A n) (f : B → A) : Policy B n where
  decide b t i x H := π.decide (f b) t i x H

lemma Policy.pullbackSeed_reward (π : Policy A n) (f : B → A) (b : B)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    (π.pullbackSeed f).reward b D x u=π.reward (f b) D x u := rfl

lemma Policy.pullbackSeed_measurable [MeasurableSpace A] [MeasurableSpace B]
    (π : Policy A n) (hπ : π.IsMeasurable) {f : B → A} (hf : Measurable f) :
    (π.pullbackSeed f).IsMeasurable := hπ.comp ((hf.comp measurable_fst).prodMk measurable_snd)

noncomputable def RandomizedPolicy.pullbackSeed (π : RandomizedPolicy n)
    {B : Type} [MeasurableSpace B] (ν : Measure B) [IsProbabilityMeasure ν]
    (f : B → π.Seed) (hf : Measurable f) : RandomizedPolicy n where
  Seed := B
  seedLaw := ν
  rule := π.rule.pullbackSeed f
  measurable_rule := π.rule.pullbackSeed_measurable π.measurable_rule hf

lemma RandomizedPolicy.pullbackSeed_expectedReward (π : RandomizedPolicy n)
    {B : Type} [MeasurableSpace B] (ν : Measure B) [IsProbabilityMeasure ν]
    (f : B → π.Seed) (hf : Measurable f) (hLaw : MeasurePreserving f ν π.seedLaw) (P : Instance n) :
    (π.pullbackSeed ν f hf).expectedReward P=π.expectedReward P := by
  have hWorld : MeasurePreserving (Prod.map id (Prod.map id f)) (P.worldLaw ν) (P.worldLaw π.seedLaw) :=
    (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.clocksLaw n)).prod hLaw)
  exact hWorld.hasLaw.integral_comp π.measurable_realizedReward.aestronglyMeasurable

lemma RandomizedPolicy.pullbackSeed_reachProbability (π : RandomizedPolicy n)
    {B : Type} [MeasurableSpace B] (ν : Measure B) [IsProbabilityMeasure ν]
    (f : B → π.Seed) (hf : Measurable f) (hLaw : MeasurePreserving f ν π.seedLaw) (P : Instance n) (i : Fin n) :
    (π.pullbackSeed ν f hf).rule.reachProbability P ν i=π.rule.reachProbability P π.seedLaw i := by
  have hWorld : MeasurePreserving (Prod.map id (Prod.map id f)) (P.worldLaw ν) (P.worldLaw π.seedLaw) :=
    (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.clocksLaw n)).prod hLaw)
  have hE : MeasurableSet {ω : ProphetSecretary.Model.World n π.Seed | π.rule.Reaches ω.2.2 ω.1 ω.2.1 i} :=
    π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  exact congrArg ENNReal.toReal (hWorld.measure_preimage hE.nullMeasurableSet)

end ProphetSecretary.Model
