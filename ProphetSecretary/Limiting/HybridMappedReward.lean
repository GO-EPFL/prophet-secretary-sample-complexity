import ProphetSecretary.Limiting.HybridScalarMixture
import ProphetSecretary.Limiting.HybridPotentialVerification
import ProphetSecretary.Model.MappedRewardFunctional

/-!
# Excess rewards along the original hybrid execution

Only the analytical selected payoff is mapped. The rule still receives all
original retained values and every original anonymous observation, including
marks below the terminal reserve. No mapped-zero Poisson model is introduced.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*}

lemma HybridRule.reward_le_terminal_add_excess (π : HybridRule n Seed) {a : ℝ} (ha : 0 ≤ a)
    (r : Seed) (x u : Fin n → ℝ) (ω : Configuration) :
    π.reward a r x u ω ≤ a + Model.excessValueMap a (π.reward 0 r x u ω) := by
  by_cases hs : π.HasSelection r x u ω
  · simp only [HybridRule.reward, hs, if_true]
    exact Model.value_le_terminal_add_excess _
  · simp only [HybridRule.reward, hs, if_false, Model.excessValueMap_zero ha, add_zero, le_refl]

noncomputable def RandomizedHybridPolicy.mappedExcessScalarObjective (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (a w c : ℝ) : ℝ :=
  ∫ v, w * Model.excessValueMap a (π.rule.realizedReward 0 v) + c * π.rule.realizedDuration v ∂B.law π.seedLaw

lemma RandomizedHybridPolicy.integrable_mappedExcessReward (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) {a : ℝ} (ha : 0 ≤ a) :
    Integrable (fun v => Model.excessValueMap a (π.rule.realizedReward 0 v)) (B.law π.seedLaw) := by
  have hR : Integrable (π.rule.realizedReward 0) (B.law π.seedLaw) :=
    π.rule.integrable_realizedReward π.measurable_rule B.individuals B.intensity π.seedLaw le_rfl B.cap.property B.cap.property
      B.individual_bounded B.intensity_supported
  have hm : Measurable (fun v => Model.excessValueMap a (π.rule.realizedReward 0 v)) :=
    (Model.measurable_excessValueMap a).comp (π.rule.measurable_realizedReward π.measurable_rule 0)
  apply (hR.abs.add (integrable_const a)).mono' hm.aestronglyMeasurable
  exact Filter.Eventually.of_forall fun v => by
    rw [Real.norm_eq_abs]
    have hd := Model.excessValueMap_displacement ha (π.rule.realizedReward 0 v)
    calc
      _ = |(Model.excessValueMap a (π.rule.realizedReward 0 v) - π.rule.realizedReward 0 v) + π.rule.realizedReward 0 v| := by congr 1; ring
      _ ≤ |Model.excessValueMap a (π.rule.realizedReward 0 v) - π.rule.realizedReward 0 v| + |π.rule.realizedReward 0 v| := abs_add_le _ _
      _ ≤ a + |π.rule.realizedReward 0 v| := add_le_add hd le_rfl
      _ = _ := add_comm _ _

lemma RandomizedHybridPolicy.terminalScalarObjective_le_mappedExcess (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) {w c : ℝ} (hw : 0 ≤ w) :
    π.scalarObjective B w c ≤ w * (B.terminal : ℝ) + π.mappedExcessScalarObjective B B.terminal w c := by
  have hI : Integrable (fun v => w * Model.excessValueMap B.terminal (π.rule.realizedReward 0 v) +
      c * π.rule.realizedDuration v) (B.law π.seedLaw) :=
    ((π.integrable_mappedExcessReward B B.terminal.property).const_mul w).add ((π.integrable_duration B).const_mul c)
  have hJ : Integrable (fun v => w * π.rule.realizedReward B.terminal v + c * π.rule.realizedDuration v)
      (B.law π.seedLaw) := ((π.integrable_reward B).const_mul w).add ((π.integrable_duration B).const_mul c)
  have h := integral_mono hJ ((integrable_const (w * (B.terminal : ℝ))).add hI) (fun v => by
    have hp := mul_le_mul_of_nonneg_left
      (π.rule.reward_le_terminal_add_excess B.terminal.property v.2.2.2 v.2.1 v.2.2.1 v.1) hw
    change w * π.rule.realizedReward B.terminal v + c * π.rule.realizedDuration v ≤
      w * (B.terminal : ℝ) + (w * Model.excessValueMap B.terminal (π.rule.realizedReward 0 v) + c * π.rule.realizedDuration v)
    change w * π.rule.realizedReward B.terminal v ≤
      w * ((B.terminal : ℝ) + Model.excessValueMap B.terminal (π.rule.realizedReward 0 v)) at hp
    linarith only [hp])
  change π.scalarObjective B w c ≤ ∫ v, w * (B.terminal : ℝ) +
    (w * Model.excessValueMap B.terminal (π.rule.realizedReward 0 v) + c * π.rule.realizedDuration v) ∂B.law π.seedLaw at h
  rw [integral_add (integrable_const _) hI, integral_const] at h
  simp only [probReal_univ,one_smul] at h
  exact h

lemma RandomizedHybridPolicy.mappedExcess_finiteEvaluation_integral (π : RandomizedHybridPolicy n)
    (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x)
    (N : ℕ) {a : ℝ} (ha : 0 ≤ a) (w c : ℝ) :
    (∫ v, w * Model.excessValueMap a (π.rule.realizedReward 0 (configurationMk N v.1,v.2)) +
      c * π.rule.realizedDuration (configurationMk N v.1,v.2)
      ∂(Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod (P.worldLaw π.seedLaw)) =
      (π.finiteEvaluation N).mappedScalarObjective (appendIID P κ hκ N) (fun _ => Model.excessValueMap a) w c := by
  let f : (π.finiteEvaluation N).World → ℝ := fun v =>
    w * Model.excessValueMap a ((π.finiteEvaluation N).realizedReward v) + c * (π.finiteEvaluation N).realizedDuration v
  have hf : Measurable f := (((Model.measurable_excessValueMap a).comp
    (π.finiteEvaluation N).measurable_realizedReward).const_mul w).add
      ((π.finiteEvaluation N).measurable_realizedDuration.const_mul c)
  have hmp := finiteArrayWorld_measurePreserving P κ hκ π.seedLaw N
  have he := integral_map (μ := (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod
    (P.worldLaw π.seedLaw)) hmp.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hmp.map_eq] at he
  rw [(π.finiteEvaluation N).mappedScalarObjective_excess_eq_integral _ ha w c]
  calc
    _ = ∫ v, f (combinedValues v.2.1 v.1,(combinedClocks v.2.2.1 v.1,v.2.2.2))
        ∂(Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod (P.worldLaw π.seedLaw) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun v => by
        dsimp only [f]
        rw [π.finiteEvaluation_reward N v,π.finiteEvaluation_duration N v]
    _ = _ := he.symm

lemma RandomizedHybridPolicy.hasSum_mappedExcess_branches (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) {a : ℝ} (ha : 0 ≤ a) (w c : ℝ) :
    HasSum (fun N : ℕ => poissonWeight B.intensity.mass N *
      (π.finiteEvaluation N).mappedScalarObjective
        (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N)
          (fun _ => Model.excessValueMap a) w c) (π.mappedExcessScalarObjective B a w c) := by
  let f : HybridWorld n π.Seed → ℝ := fun v =>
    w * Model.excessValueMap a (π.rule.realizedReward 0 v) + c * π.rule.realizedDuration v
  have hm : Measurable f := (((Model.measurable_excessValueMap a).comp
    (π.rule.measurable_realizedReward π.measurable_rule 0)).const_mul w).add
      ((π.rule.measurable_realizedDuration π.measurable_rule).const_mul c)
  have hi : Integrable f (B.law π.seedLaw) :=
    ((π.integrable_mappedExcessReward B ha).const_mul w).add ((π.integrable_duration B).const_mul c)
  have hs := hasSum_worldLaw_fibers B.intensity (B.individuals.worldLaw π.seedLaw) f hm hi
  have he (N : ℕ) : (∫ v, f (configurationMk N v.1,v.2) ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw π.seedLaw)) =
      (π.finiteEvaluation N).mappedScalarObjective
        (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N)
          (fun _ => Model.excessValueMap a) w c :=
    π.mappedExcess_finiteEvaluation_integral _ _ (B.normalizedMark_nonnegative hμ) N ha w c
  convert! hs using 1
  · funext N
    rw [he N]

end ProphetSecretary.Limiting
