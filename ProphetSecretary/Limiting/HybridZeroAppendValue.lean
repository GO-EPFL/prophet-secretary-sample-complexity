import ProphetSecretary.Limiting.HybridIgnoreIndividuals

/-!
# Appending zero individual identities preserves hybrid optimal value

The forward embedding rejects the added identities and ignores their retained
history. Its outcomes are preserved by an actual product-law transport. The
reverse direction uses the previously constructed independent-clock simulation.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

def forgetZeroAuxiliaryHybridSeed (v : HybridWorld n (Seed × (Fin k → ℝ))) : HybridWorld n Seed :=
  (v.1,(v.2.1,(v.2.2.1,v.2.2.2.1)))

lemma forgetZeroAuxiliaryHybridSeed_measurePreserving (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) :
    MeasurePreserving (forgetZeroAuxiliaryHybridSeed (n := n) (k := k))
      (hybridWorldLaw P μ (ν.prod (Model.Instance.clocksLaw k))) (hybridWorldLaw P μ ν) :=
  (MeasurePreserving.id (configurationLaw μ)).prod
    ((MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Model.Instance.clocksLaw n)).prod measurePreserving_fst))

noncomputable def RandomizedHybridPolicy.ignoreIndividualExtras (π : RandomizedHybridPolicy n) (k : ℕ) :
    RandomizedHybridPolicy (n + k) where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.ignoreIndividualExtras (Fin.castAddEmb k)
  measurable_rule := π.rule.ignoreIndividualExtras_isMeasurable π.measurable_rule _

lemma RandomizedHybridPolicy.scalarObjective_ignoreIndividualExtras (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (k : ℕ) (ha : B.terminal = 0) (w c : ℝ) :
    (π.ignoreIndividualExtras k).scalarObjective (B.appendZeroIndividuals k) w c = π.scalarObjective B w c := by
  let m := B.law (π.seedLaw.prod (Model.Instance.clocksLaw k))
  let F : HybridWorld (n + k) π.Seed → ℝ := fun v =>
    w * (π.ignoreIndividualExtras k).rule.realizedReward 0 v + c * (π.ignoreIndividualExtras k).rule.realizedDuration v
  let G : HybridWorld n π.Seed → ℝ := fun v => w * π.rule.realizedReward 0 v + c * π.rule.realizedDuration v
  have hFm : Measurable F := (((π.ignoreIndividualExtras k).rule.measurable_realizedReward
    (π.ignoreIndividualExtras k).measurable_rule 0).const_mul w).add
      (((π.ignoreIndividualExtras k).rule.measurable_realizedDuration (π.ignoreIndividualExtras k).measurable_rule).const_mul c)
  have hGm : Measurable G := ((π.rule.measurable_realizedReward π.measurable_rule 0).const_mul w).add
    ((π.rule.measurable_realizedDuration π.measurable_rule).const_mul c)
  have hAug : MeasurePreserving (augmentZeroHybridWorld (n := n) (k := k)) m
      ((B.appendZeroIndividuals k).law π.seedLaw) :=
    augmentZeroHybridWorld_measurePreserving B.individuals B.intensity π.seedLaw k
  have hBase : MeasurePreserving (forgetZeroAuxiliaryHybridSeed (n := n) (k := k)) m (B.law π.seedLaw) :=
    forgetZeroAuxiliaryHybridSeed_measurePreserving B.individuals B.intensity π.seedLaw k
  have hF := integral_map (μ := m) hAug.measurable.aemeasurable hFm.aestronglyMeasurable
  have hG := integral_map (μ := m) hBase.measurable.aemeasurable hGm.aestronglyMeasurable
  rw [hAug.map_eq] at hF
  rw [hBase.map_eq] at hG
  unfold RandomizedHybridPolicy.scalarObjective
  rw [show (B.appendZeroIndividuals k).terminal = B.terminal from rfl, ha]
  change (∫ v, F v ∂(B.appendZeroIndividuals k).law π.seedLaw) = ∫ v, G v ∂B.law π.seedLaw
  rw [hF,hG]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    change w * (π.rule.ignoreIndividualExtras (Fin.castAddEmb k)).reward 0 v.2.2.2.1
      (Model.ZeroSimulation.appendValues v.2.1) (Model.ZeroSimulation.appendClocks v.2.2.1 v.2.2.2.2) v.1 +
      c * (π.rule.ignoreIndividualExtras (Fin.castAddEmb k)).stoppingTime v.2.2.2.1
        (Model.ZeroSimulation.appendValues v.2.1) (Model.ZeroSimulation.appendClocks v.2.2.1 v.2.2.2.2) v.1 =
      w * π.rule.reward 0 v.2.2.2.1 v.2.1 v.2.2.1 v.1 + c * π.rule.stoppingTime v.2.2.2.1 v.2.1 v.2.2.1 v.1
    rw [π.rule.ignoreIndividualExtras_reward_zero, π.rule.ignoreIndividualExtras_stoppingTime]

lemma FiniteIntensityHybridInstance.value_le_appendZeroIndividuals (B : FiniteIntensityHybridInstance n)
    (k : ℕ) (ha : B.terminal = 0) (w c : ℝ) :
    B.optimalScalarValue w c ≤ (B.appendZeroIndividuals k).optimalScalarValue w c := by
  apply csSup_le (B.scalarPayoffs_nonempty w c)
  rintro _ ⟨π,rfl⟩
  change π.scalarObjective B w c ≤ _
  rw [← π.scalarObjective_ignoreIndividualExtras B k ha w c]
  exact (B.appendZeroIndividuals k).scalarObjective_le_value _ w c

/-- All zero histories are retained in the model; the equality follows from
two causal policy constructions, not from silently deleting observations. -/
theorem FiniteIntensityHybridInstance.value_appendZeroIndividuals (B : FiniteIntensityHybridInstance n)
    (k : ℕ) (ha : B.terminal = 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (B.appendZeroIndividuals k).optimalScalarValue w c = B.optimalScalarValue w c :=
  le_antisymm (B.value_appendZeroIndividuals_le k ha hw hc) (B.value_le_appendZeroIndividuals k ha w c)

end ProphetSecretary.Limiting
