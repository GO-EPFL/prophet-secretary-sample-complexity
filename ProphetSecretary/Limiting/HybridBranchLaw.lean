import ProphetSecretary.Limiting.FiniteArrayEvaluation
import ProphetSecretary.Limiting.HybridScalarObjectives

/-!
# Conditional finite-array evaluation of a fixed hybrid policy

The finite policies below are derived adapters of one hybrid rule. They are
used only to integrate the analytical count branches; no observation of the
realized total count or of anonymous generation labels is introduced.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma normalized_ae (μ : FiniteMeasure ℝ) (hμ : μ ≠ 0) {p : ℝ → Prop}
    (hp : ∀ᵐ x ∂(μ : Measure ℝ), p x) : ∀ᵐ x ∂(μ.normalize : Measure ℝ), p x := by
  rw [μ.toMeasure_normalize_eq_of_nonzero hμ]
  exact Measure.ae_smul_measure hp _

namespace RandomizedHybridPolicy

noncomputable def finiteEvaluation (π : RandomizedHybridPolicy n) (N : ℕ) : Model.RandomizedPolicy (n + N) where
  Seed := π.Seed
  seedLaw := π.seedLaw
  rule := π.rule.asFinitePolicy N
  measurable_rule := π.rule.asFinitePolicy_isMeasurable π.measurable_rule N

lemma finiteEvaluation_reward (π : RandomizedHybridPolicy n) (N : ℕ)
    (v : (Fin N → Point) × Model.World n π.Seed) :
    (π.finiteEvaluation N).realizedReward (combinedValues v.2.1 v.1, (combinedClocks v.2.2.1 v.1, v.2.2.2)) =
      π.rule.realizedReward 0 (configurationMk N v.1, v.2) := by
  change (π.rule.asFinitePolicy N).reward v.2.2.2 Finset.univ (combinedValues v.2.1 v.1) (combinedClocks v.2.2.1 v.1) =
    π.rule.reward 0 v.2.2.2 v.2.1 v.2.2.1 (configurationMk N v.1)
  unfold HybridRule.reward
  split_ifs with hs
  · rfl
  · apply Model.Policy.reward_eq_zero_of_no_actualSelection
    intro i hi
    exact hs ⟨i, hi⟩

lemma finiteEvaluation_duration (π : RandomizedHybridPolicy n) (N : ℕ)
    (v : (Fin N → Point) × Model.World n π.Seed) :
    (π.finiteEvaluation N).realizedDuration (combinedValues v.2.1 v.1, (combinedClocks v.2.2.1 v.1, v.2.2.2)) =
      π.rule.realizedDuration (configurationMk N v.1, v.2) := rfl

lemma finiteEvaluation_integral (π : RandomizedHybridPolicy n) (P : Model.Instance n)
    (κ : Measure ℝ) [IsProbabilityMeasure κ] (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (N : ℕ) (w c : ℝ) :
    (∫ v, w * π.rule.realizedReward 0 (configurationMk N v.1, v.2) +
      c * π.rule.realizedDuration (configurationMk N v.1, v.2)
      ∂(Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod (P.worldLaw π.seedLaw)) =
    (π.finiteEvaluation N).scalarObjective (appendIID P κ hκ N) w c := by
  let f := fun ω : (π.finiteEvaluation N).World =>
    w * (π.finiteEvaluation N).realizedReward ω + c * (π.finiteEvaluation N).realizedDuration ω
  have hf : Measurable f := ((π.finiteEvaluation N).measurable_realizedReward.const_mul w).add
    ((π.finiteEvaluation N).measurable_realizedDuration.const_mul c)
  have hmp := finiteArrayWorld_measurePreserving P κ hκ π.seedLaw N
  have h := integral_map (μ := (Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod
    (P.worldLaw π.seedLaw)) hmp.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hmp.map_eq] at h
  calc
    _ = ∫ v, f (combinedValues v.2.1 v.1, (combinedClocks v.2.2.1 v.1, v.2.2.2))
        ∂(Measure.pi (fun _ : Fin N => Model.Instance.uniformClock.prod κ)).prod (P.worldLaw π.seedLaw) := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun v => by
        dsimp only [f]
        rw [π.finiteEvaluation_reward N v, π.finiteEvaluation_duration N v])
    _ = _ := h.symm

lemma poisson_branch_integral (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity ≠ 0) (N : ℕ) (w c : ℝ) :
    (∫ v, w * π.rule.realizedReward 0 (configurationMk N v.1, v.2) +
      c * π.rule.realizedDuration (configurationMk N v.1, v.2)
      ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw π.seedLaw)) =
    (π.finiteEvaluation N).scalarObjective
      (appendIID B.individuals (B.intensity.normalize : Measure ℝ)
        ((normalized_ae B.intensity hμ B.intensity_supported).mono (fun _ hx => hx.1.le)) N) w c :=
  π.finiteEvaluation_integral _ _ _ _ _ _

end RandomizedHybridPolicy
end ProphetSecretary.Limiting
