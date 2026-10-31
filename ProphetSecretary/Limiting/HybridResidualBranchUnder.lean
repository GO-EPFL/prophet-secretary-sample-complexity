import ProphetSecretary.Limiting.HybridResidualUnder

/-!
# Count-branch transport of a target residual under original observations

The target offer and mark laws may differ from the actual observed laws. The
actual original finite-array/world map transports the fixed policy's residual;
no policy sees its realized anonymous count or transformed future values.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma RandomizedHybridPolicy.designResidual_branchIntegral_under (π : RandomizedHybridPolicy n)
    (Q T P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hT : Integrable Model.Instance.maximum T.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ)
    (κ₀ : Measure ℝ) [IsProbabilityMeasure κ₀] (hκ₀ : ∀ᵐ x ∂κ₀, 0 ≤ x)
    (N : ℕ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ v, π.rule.designResidual Q T κ hκ w c (configurationMk N v.1,v.2)
      ∂(Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ₀)).prod (P.worldLaw π.seedLaw)) =
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.reachedTransitionResidual
        (Q.appendZeros N) (appendIID T κ hκ N) w c ω.2.2 ω.1 ω.2.1
          ∂(appendIID P κ₀ hκ₀ N).worldLaw π.seedLaw := by
  have hI' : Integrable (fun x : ℝ => x) κ := by convert! hI using 1
  have hm : Measurable (fun ω : (π.finiteEvaluation N).World =>
      (π.finiteEvaluation N).rule.reachedTransitionResidual (Q.appendZeros N) (appendIID T κ hκ N) w c
        ω.2.2 ω.1 ω.2.1) :=
    (π.finiteEvaluation N).rule.measurable_reachedTransitionResidual (π.finiteEvaluation N).measurable_rule
      (Q.appendZeros N) (appendIID T κ hκ N) (Q.appendZeros_integrable_maximum N hQ)
      (appendIID_integrable_maximum T κ hκ N hT hI') hw hc (by fun_prop) (fun _ => by fun_prop) (fun _ => by fun_prop)
  have hp := finiteArrayWorld_measurePreserving P κ₀ hκ₀ π.seedLaw N
  have he := integral_map (μ := (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ₀)).prod
    (P.worldLaw π.seedLaw)) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  exact he.symm

lemma RandomizedHybridPolicy.hasSum_designResidual_under (π : RandomizedHybridPolicy n)
    (Q T : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hT : Integrable Model.Instance.maximum T.valuesLaw)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (hI : Integrable id κ)
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    HasSum (fun N : ℕ => poissonWeight B.intensity.mass N *
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.reachedTransitionResidual
        (Q.appendZeros N) (appendIID T κ hκ N) w c ω.2.2 ω.1 ω.2.1
          ∂(appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N).worldLaw π.seedLaw)
      (∫ v, π.rule.designResidual Q T κ hκ w c v ∂B.law π.seedLaw) := by
  have hm := π.rule.measurable_designResidual π.measurable_rule Q T hQ hT κ hκ hI hw hc
  have hi := (π.rule.designResidual_generator_under π.measurable_rule Q T B.individuals hQ hT
    κ hκ hI B.intensity π.seedLaw hw hc).1
  have hs := hasSum_worldLaw_fibers B.intensity (B.individuals.worldLaw π.seedLaw) _ hm hi
  have he (N : ℕ) : (∫ v, π.rule.designResidual Q T κ hκ w c (configurationMk N v.1,v.2)
      ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw π.seedLaw)) =
      ∫ ω : (π.finiteEvaluation N).World, (π.finiteEvaluation N).rule.reachedTransitionResidual
        (Q.appendZeros N) (appendIID T κ hκ N) w c ω.2.2 ω.1 ω.2.1
          ∂(appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N).worldLaw π.seedLaw :=
    π.designResidual_branchIntegral_under Q T B.individuals hQ hT κ hκ hI _ (B.normalizedMark_nonnegative hμ) N hw hc
  convert! hs using 1
  funext N
  rw [he N]

end ProphetSecretary.Limiting
