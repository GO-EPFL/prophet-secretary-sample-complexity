import ProphetSecretary.Limiting.HybridMappedReward
import ProphetSecretary.Limiting.HybridZeroAppendValue
import ProphetSecretary.Limiting.PositiveExcessPolicies
import ProphetSecretary.Model.ExcessOrder

/-!
# Causal virtual-zero transports for mapped rewards

The original reward/duration comparisons imply the mapped comparison because
the excess map is monotone. The actual auxiliary virtual clocks are independent
of retained offers and anonymous points. Positive-excess callbacks also give
an exact fixed-terminal scalar-payoff identity.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ}

lemma RandomizedHybridPolicy.mappedExcess_ignoreIndividualExtras (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (k : ℕ) (a w c : ℝ) :
    (π.ignoreIndividualExtras k).mappedExcessScalarObjective (B.appendZeroIndividuals k) a w c =
      π.mappedExcessScalarObjective B a w c := by
  let m := B.law (π.seedLaw.prod (Model.Instance.clocksLaw k))
  let F : HybridWorld (n + k) π.Seed → ℝ := fun v =>
    w * Model.excessValueMap a ((π.ignoreIndividualExtras k).rule.realizedReward 0 v) +
      c * (π.ignoreIndividualExtras k).rule.realizedDuration v
  let G : HybridWorld n π.Seed → ℝ := fun v =>
    w * Model.excessValueMap a (π.rule.realizedReward 0 v) + c * π.rule.realizedDuration v
  have hFm : Measurable F := (((Model.measurable_excessValueMap a).comp
    ((π.ignoreIndividualExtras k).rule.measurable_realizedReward (π.ignoreIndividualExtras k).measurable_rule 0)).const_mul w).add
      (((π.ignoreIndividualExtras k).rule.measurable_realizedDuration (π.ignoreIndividualExtras k).measurable_rule).const_mul c)
  have hGm : Measurable G := (((Model.measurable_excessValueMap a).comp
    (π.rule.measurable_realizedReward π.measurable_rule 0)).const_mul w).add
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
  change (∫ v, F v ∂(B.appendZeroIndividuals k).law π.seedLaw) = ∫ v, G v ∂B.law π.seedLaw
  rw [hF,hG]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    change w * Model.excessValueMap a ((π.rule.ignoreIndividualExtras (Fin.castAddEmb k)).reward 0 v.2.2.2.1
      (Model.ZeroSimulation.appendValues v.2.1) (Model.ZeroSimulation.appendClocks v.2.2.1 v.2.2.2.2) v.1) +
      c * (π.rule.ignoreIndividualExtras (Fin.castAddEmb k)).stoppingTime v.2.2.2.1
        (Model.ZeroSimulation.appendValues v.2.1) (Model.ZeroSimulation.appendClocks v.2.2.1 v.2.2.2.2) v.1 =
      w * Model.excessValueMap a (π.rule.reward 0 v.2.2.2.1 v.2.1 v.2.2.1 v.1) + c * π.rule.stoppingTime v.2.2.2.1 v.2.1 v.2.2.1 v.1
    rw [π.rule.ignoreIndividualExtras_reward_zero,π.rule.ignoreIndividualExtras_stoppingTime]

lemma RandomizedHybridPolicy.mappedExcess_le_simulateZeroIndividuals (π : RandomizedHybridPolicy (n + k))
    (B : FiniteIntensityHybridInstance n) {a w c : ℝ} (ha : 0 ≤ a) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.mappedExcessScalarObjective (B.appendZeroIndividuals k) a w c ≤
      π.simulateZeroIndividuals.mappedExcessScalarObjective B a w c := by
  let m := B.law (π.seedLaw.prod (Model.Instance.clocksLaw k))
  let F : HybridWorld (n + k) π.Seed → ℝ := fun v =>
    w * Model.excessValueMap a (π.rule.realizedReward 0 v) + c * π.rule.realizedDuration v
  let G : HybridWorld n (π.Seed × (Fin k → ℝ)) → ℝ := fun v =>
    w * Model.excessValueMap a ((HybridZeroSimulation.simulate π.rule).realizedReward 0 v) +
      c * (HybridZeroSimulation.simulate π.rule).realizedDuration v
  have hFInt : Integrable F ((B.appendZeroIndividuals k).law π.seedLaw) :=
    ((π.integrable_mappedExcessReward (B.appendZeroIndividuals k) ha).const_mul w).add
      ((π.integrable_duration (B.appendZeroIndividuals k)).const_mul c)
  have hGInt : Integrable G m :=
    (((π.simulateZeroIndividuals).integrable_mappedExcessReward B ha).const_mul w).add
      (((π.simulateZeroIndividuals).integrable_duration B).const_mul c)
  have hFm : Measurable F := (((Model.measurable_excessValueMap a).comp
    (π.rule.measurable_realizedReward π.measurable_rule 0)).const_mul w).add
      ((π.rule.measurable_realizedDuration π.measurable_rule).const_mul c)
  have hp : MeasurePreserving (augmentZeroHybridWorld (n := n) (k := k)) m
      ((B.appendZeroIndividuals k).law π.seedLaw) :=
    augmentZeroHybridWorld_measurePreserving B.individuals B.intensity π.seedLaw k
  have hb := realized_values_bounds B.individuals B.intensity (π.seedLaw.prod (Model.Instance.clocksLaw k))
    B.individual_bounded B.intensity_supported
  have hpoint : (fun v => F (augmentZeroHybridWorld v)) ≤ᵐ[m] G := by
    filter_upwards [hb] with v hv
    have hr := HybridZeroSimulation.reward_le_simulated π.rule v.2.2.2.1 v.2.1 v.2.2.1 v.2.2.2.2 v.1 (fun i => (hv i).1)
    have ht := HybridZeroSimulation.stoppingTime_le_simulated π.rule v.2.2.2.1 v.2.1 v.2.2.1 v.2.2.2.2 v.1
    exact add_le_add (mul_le_mul_of_nonneg_left (Model.excessValueMap_monotone ha hr) hw)
      (mul_le_mul_of_nonneg_left ht hc)
  have h := integral_mono_ae (hp.integrable_comp_of_integrable hFInt) hGInt hpoint
  have he := integral_map (μ := m) hp.measurable.aemeasurable hFm.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.le.trans h

lemma RandomizedHybridPolicy.scalarObjective_eq_terminal_add_mappedExcess (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (hπ : π.rule.AcceptsPositiveExcess B.terminal) (w c : ℝ) :
    π.scalarObjective B w c = w * (B.terminal : ℝ) + π.mappedExcessScalarObjective B B.terminal w c := by
  have hI : Integrable (fun v => w * Model.excessValueMap B.terminal (π.rule.realizedReward 0 v) +
      c * π.rule.realizedDuration v) (B.law π.seedLaw) :=
    ((π.integrable_mappedExcessReward B B.terminal.property).const_mul w).add ((π.integrable_duration B).const_mul c)
  have heq : (fun v : HybridWorld n π.Seed => w * π.rule.realizedReward B.terminal v + c * π.rule.realizedDuration v) =
      (fun v => w * (B.terminal : ℝ) + (w * Model.excessValueMap B.terminal (π.rule.realizedReward 0 v) + c * π.rule.realizedDuration v)) := by
    funext v
    change w * π.rule.reward B.terminal v.2.2.2 v.2.1 v.2.2.1 v.1 + c * π.rule.realizedDuration v = _
    have hp := π.rule.reward_eq_terminal_add_excess B.terminal.property hπ v.2.2.2 v.2.1 v.2.2.1 v.1
    have h := congrArg (fun r : ℝ => w * r + c * π.rule.realizedDuration v) hp
    apply h.trans
    change w * ((B.terminal : ℝ) + Model.excessValueMap B.terminal (π.rule.realizedReward 0 v)) + c * π.rule.realizedDuration v = _
    ring
  unfold RandomizedHybridPolicy.scalarObjective
  rw [heq,integral_add (integrable_const _) hI,integral_const]
  simp only [probReal_univ,one_smul]
  rfl

end ProphetSecretary.Limiting
