import ProphetSecretary.Model.RankRandomized
import Mathlib.Probability.HasLaw

/-!
# Pulling a rank policy back along an independent seed map

Only the auxiliary random seed is changed. Every observation and every
pathwise decision is retained; a measure-preserving seed map then retains
the actual online reward law.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n : ℕ} {A B : Type*}

def RankPolicy.pullbackSeed (π : RankPolicy A n) (f : B → A) : RankPolicy B n where
  decide b k i x H := π.decide (f b) k i x H

lemma RankPolicy.pullbackSeed_reward (π : RankPolicy A n) (f : B → A) (b : B)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    (π.pullbackSeed f).reward b p x = π.reward (f b) p x := rfl

lemma RankPolicy.pullbackSeed_measurable [MeasurableSpace A] [MeasurableSpace B]
    (π : RankPolicy A n) (hπ : π.IsMeasurable) {f : B → A} (hf : Measurable f) :
    (π.pullbackSeed f).IsMeasurable :=
  hπ.comp ((hf.comp measurable_fst).prodMk measurable_snd)

noncomputable def RandomizedRankPolicy.pullbackSeed (π : RandomizedRankPolicy n)
    {B : Type} [MeasurableSpace B] (ν : Measure B) [IsProbabilityMeasure ν]
    (f : B → π.Seed) (hf : Measurable f) : RandomizedRankPolicy n where
  Seed := B
  seedLaw := ν
  rule := π.rule.pullbackSeed f
  measurable_rule := π.rule.pullbackSeed_measurable π.measurable_rule hf

lemma RandomizedRankPolicy.pullbackSeed_expectedReward (π : RandomizedRankPolicy n)
    {B : Type} [MeasurableSpace B] (ν : Measure B) [IsProbabilityMeasure ν]
    (f : B → π.Seed) (hf : Measurable f) (hLaw : MeasurePreserving f ν π.seedLaw) (P : Instance n) :
    (π.pullbackSeed ν f hf).expectedReward P = π.expectedReward P := by
  have hWorld : MeasurePreserving (Prod.map id (Prod.map id f))
      ((π.pullbackSeed ν f hf).worldLaw P) (π.worldLaw P) := by
    change MeasurePreserving (Prod.map id (Prod.map id f))
      (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ν))
      (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod π.seedLaw))
    exact (MeasurePreserving.id P.valuesLaw).prod
      ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod hLaw)
  exact hWorld.hasLaw.integral_comp π.measurable_realizedReward.aestronglyMeasurable

lemma RandomizedRankPolicy.pullbackSeed_reach_probability (π : RandomizedRankPolicy n)
    {B : Type} [MeasurableSpace B] (ν : Measure B) [IsProbabilityMeasure ν]
    (f : B → π.Seed) (hf : Measurable f) (hLaw : MeasurePreserving f ν π.seedLaw)
    (P : Instance n) (i : Fin n) :
    ((π.pullbackSeed ν f hf).worldLaw P).real
      {ω | (π.pullbackSeed ν f hf).rule.Reaches ω.2.2 ω.2.1 ω.1 i} =
    (π.worldLaw P).real {ω | π.rule.Reaches ω.2.2 ω.2.1 ω.1 i} := by
  have hWorld : MeasurePreserving (Prod.map id (Prod.map id f))
      ((π.pullbackSeed ν f hf).worldLaw P) (π.worldLaw P) := by
    change MeasurePreserving (Prod.map id (Prod.map id f))
      (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ν))
      (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod π.seedLaw))
    exact (MeasurePreserving.id P.valuesLaw).prod
      ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod hLaw)
  have hm : MeasurableSet {ω : π.World | π.rule.Reaches ω.2.2 ω.2.1 ω.1 i} :=
    π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
      (measurable_fst.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst) i
  exact congrArg ENNReal.toReal (hWorld.measure_preimage hm.nullMeasurableSet)

end ProphetSecretary.Model
