import ProphetSecretary.Limiting.HybridZeroSimulation
import ProphetSecretary.Limiting.HybridScalarObjectives
import ProphetSecretary.Model.ZeroSimulationProbability

/-!
# Probability transport for hybrid zero-identity simulation

Virtual individual clocks are independent auxiliary randomness. The actual
marked-Poisson configuration remains unchanged, and the explicit world map
has the augmented product law. Causal simulation can therefore remove all
appended zero identities without decreasing a nonnegative scalar objective.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def FiniteIntensityHybridInstance.appendZeroIndividuals (B : FiniteIntensityHybridInstance n) (k : ℕ) :
    FiniteIntensityHybridInstance (n + k) where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals := B.individuals.appendZeros k
  individual_bounded := by
    intro i
    induction i using Fin.addCases with
    | left i => simpa only [Model.Instance.appendZeros, Fin.addCases_left] using B.individual_bounded i
    | right j => simp [Model.Instance.appendZeros]
  intensity := B.intensity
  intensity_supported := B.intensity_supported

def augmentZeroHybridWorld (v : HybridWorld n (Seed × (Fin k → ℝ))) : HybridWorld (n + k) Seed :=
  (v.1, Model.Instance.augmentZeroWorld v.2)

lemma augmentZeroHybridWorld_measurePreserving (P : Model.Instance n) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (k : ℕ) :
    MeasurePreserving (augmentZeroHybridWorld (n := n) (k := k))
      (hybridWorldLaw P μ (ν.prod (Model.Instance.clocksLaw k)))
      (hybridWorldLaw (P.appendZeros k) μ ν) :=
  (MeasurePreserving.id (configurationLaw μ)).prod (P.augmentZeroWorld_measurePreserving ν k)

noncomputable def RandomizedHybridPolicy.simulateZeroIndividuals (π : RandomizedHybridPolicy (n + k)) :
    RandomizedHybridPolicy n where
  Seed := π.Seed × (Fin k → ℝ)
  seedLaw := π.seedLaw.prod (Model.Instance.clocksLaw k)
  rule := HybridZeroSimulation.simulate π.rule
  measurable_rule := HybridZeroSimulation.simulate_isMeasurable π.rule π.measurable_rule

lemma RandomizedHybridPolicy.duration_le_simulateZeroIndividuals (π : RandomizedHybridPolicy (n + k))
    (B : FiniteIntensityHybridInstance n) :
    π.expectedDuration (B.appendZeroIndividuals k) ≤ (π.simulateZeroIndividuals).expectedDuration B := by
  let m := B.law (π.seedLaw.prod (Model.Instance.clocksLaw k))
  have hmp : MeasurePreserving (augmentZeroHybridWorld (n := n) (k := k)) m
      ((B.appendZeroIndividuals k).law π.seedLaw) :=
    augmentZeroHybridWorld_measurePreserving B.individuals B.intensity π.seedLaw k
  have hsim : Integrable (HybridZeroSimulation.simulate π.rule).realizedDuration m :=
    (π.simulateZeroIndividuals).integrable_duration B
  have hi := integral_mono (hmp.integrable_comp_of_integrable (π.integrable_duration (B.appendZeroIndividuals k)))
    hsim (fun v => HybridZeroSimulation.stoppingTime_le_simulated π.rule v.2.2.2.1 v.2.1 v.2.2.1 v.2.2.2.2 v.1)
  have hm := integral_map (μ := m) hmp.measurable.aemeasurable (π.rule.measurable_realizedDuration π.measurable_rule).aestronglyMeasurable
  rw [hmp.map_eq] at hm
  change (∫ v, π.rule.realizedDuration v ∂(B.appendZeroIndividuals k).law π.seedLaw) ≤ _
  rw [hm]
  exact hi

lemma RandomizedHybridPolicy.reward_le_simulateZeroIndividuals (π : RandomizedHybridPolicy (n + k))
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) :
    π.expectedReward (B.appendZeroIndividuals k) ≤ (π.simulateZeroIndividuals).expectedReward B := by
  let m := B.law (π.seedLaw.prod (Model.Instance.clocksLaw k))
  have hmp : MeasurePreserving (augmentZeroHybridWorld (n := n) (k := k)) m
      ((B.appendZeroIndividuals k).law π.seedLaw) :=
    augmentZeroHybridWorld_measurePreserving B.individuals B.intensity π.seedLaw k
  have hR : Integrable (π.rule.realizedReward 0) ((B.appendZeroIndividuals k).law π.seedLaw) := by
    have h := π.integrable_reward (B.appendZeroIndividuals k)
    simpa only [FiniteIntensityHybridInstance.appendZeroIndividuals, ha, NNReal.coe_zero] using h
  have hsim : Integrable ((HybridZeroSimulation.simulate π.rule).realizedReward 0) m := by
    have h := (π.simulateZeroIndividuals).integrable_reward B
    simp only [ha, NNReal.coe_zero] at h
    convert! h using 1
  have hb := realized_values_bounds B.individuals B.intensity
    (π.seedLaw.prod (Model.Instance.clocksLaw k)) B.individual_bounded B.intensity_supported
  have hi := integral_mono_ae (hmp.integrable_comp_of_integrable hR) hsim
    (hb.mono (fun v hv => HybridZeroSimulation.reward_le_simulated π.rule v.2.2.2.1 v.2.1 v.2.2.1 v.2.2.2.2 v.1
      (fun i => (hv i).1)))
  have hm := integral_map (μ := m) hmp.measurable.aemeasurable (π.rule.measurable_realizedReward π.measurable_rule 0).aestronglyMeasurable
  rw [hmp.map_eq] at hm
  change (∫ v, π.rule.realizedReward ((B.appendZeroIndividuals k).terminal : ℝ) v
    ∂(B.appendZeroIndividuals k).law π.seedLaw) ≤ _
  rw [show (B.appendZeroIndividuals k).terminal = B.terminal from rfl, ha]
  change (∫ v, π.rule.realizedReward 0 v ∂(B.appendZeroIndividuals k).law π.seedLaw) ≤ _
  rw [hm]
  unfold RandomizedHybridPolicy.expectedReward HybridRule.expectedReward
  rw [ha]
  convert! hi using 1

lemma RandomizedHybridPolicy.scalarObjective_le_simulateZeroIndividuals (π : RandomizedHybridPolicy (n + k))
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.scalarObjective (B.appendZeroIndividuals k) w c ≤ (π.simulateZeroIndividuals).scalarObjective B w c := by
  rw [π.scalarObjective_eq, (π.simulateZeroIndividuals).scalarObjective_eq]
  exact add_le_add (mul_le_mul_of_nonneg_left (π.reward_le_simulateZeroIndividuals B ha) hw)
    (mul_le_mul_of_nonneg_left (π.duration_le_simulateZeroIndividuals B) hc)

lemma FiniteIntensityHybridInstance.value_appendZeroIndividuals_le (B : FiniteIntensityHybridInstance n)
    (k : ℕ) (ha : B.terminal = 0) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (B.appendZeroIndividuals k).optimalScalarValue w c ≤ B.optimalScalarValue w c := by
  apply csSup_le ((B.appendZeroIndividuals k).scalarPayoffs_nonempty w c)
  rintro _ ⟨π, rfl⟩
  exact (π.scalarObjective_le_simulateZeroIndividuals B ha hw hc).trans (B.scalarObjective_le_value _ w c)

end ProphetSecretary.Limiting
