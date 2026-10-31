import ProphetSecretary.Limiting.HybridMixture

/-!
# Scalar payoff mixture for one admissible hybrid policy

Only the actual payoff is mixed over the analytical count. Each summand uses
the adapter of the same policy, with the original independent auxiliary law.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma FiniteIntensityHybridInstance.normalizedMark_integrable (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity ≠ 0) : Integrable id (B.intensity.normalize : Measure ℝ) := by
  apply Integrable.of_bound aestronglyMeasurable_id (B.cap : ℝ)
  filter_upwards [normalized_ae B.intensity hμ B.intensity_supported] with x hx
  simpa only [id_eq, Real.norm_eq_abs, abs_of_pos hx.1] using hx.2

lemma RandomizedHybridPolicy.hasSum_scalarObjective_branches (π : RandomizedHybridPolicy n)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) (w c : ℝ) :
    HasSum (fun N : ℕ => poissonWeight B.intensity.mass N *
      (π.finiteEvaluation N).scalarObjective
        (appendIID B.individuals (B.intensity.normalize : Measure ℝ)
          ((normalized_ae B.intensity hμ B.intensity_supported).mono (fun _ hx => hx.1.le)) N) w c)
      (π.scalarObjective B w c) := by
  let f : HybridWorld n π.Seed → ℝ := fun v =>
    w * π.rule.realizedReward 0 v + c * π.rule.realizedDuration v
  have hm : Measurable f := ((π.rule.measurable_realizedReward π.measurable_rule 0).const_mul w).add
    ((π.rule.measurable_realizedDuration π.measurable_rule).const_mul c)
  have hf : Integrable f (B.law π.seedLaw) := by
    have hr := π.integrable_reward B
    rw [ha] at hr
    exact (hr.const_mul w).add ((π.integrable_duration B).const_mul c)
  have hs := hasSum_worldLaw_fibers B.intensity (B.individuals.worldLaw π.seedLaw) f hm hf
  have he (N : ℕ) : (∫ v, f (configurationMk N v.1, v.2)
      ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw π.seedLaw)) =
      (π.finiteEvaluation N).scalarObjective
        (appendIID B.individuals (B.intensity.normalize : Measure ℝ)
          ((normalized_ae B.intensity hμ B.intensity_supported).mono (fun _ hx => hx.1.le)) N) w c :=
    π.poisson_branch_integral B hμ N w c
  convert! hs using 1
  · funext N
    rw [he N]
  · unfold RandomizedHybridPolicy.scalarObjective
    rw [ha]
    rfl

end ProphetSecretary.Limiting
