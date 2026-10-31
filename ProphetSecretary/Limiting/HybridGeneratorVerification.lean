import ProphetSecretary.Limiting.HybridRetainedDrift
import ProphetSecretary.Limiting.HybridPoissonDrift

/-!
# Verification with the actual hybrid generator

Combining the derived retained-clock and marked-Poisson compensators turns the
finite Bellman potential residual into its signed stopped generator. Competing
policies retain both individual zero histories and anonymous positive arrivals.
The one shared potential threshold rule has equality.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Limiting

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def HybridRule.potentialGeneratorDrift (π : HybridRule n Seed)
    (Q P : Model.Instance n) (κ : Measure ℝ) (μ : FiniteMeasure ℝ) (w c : ℝ)
    (q : HybridWorld n Seed × ℝ) : ℝ :=
  π.retainedPotentialDrift Q P w c q - π.poissonPotentialDrift Q κ μ w c q

lemma HybridRule.designResidual_expectation_eq_generator (π : HybridRule n Seed) (hπ : π.IsMeasurable)
    (Q P : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ a ∂κ, 0 ≤ a) (hI : Integrable id κ) (μ : FiniteMeasure ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Integrable (π.potentialGeneratorDrift Q P κ μ w c)
      ((hybridWorldLaw P μ ν).prod Model.Instance.uniformClock) ∧
      (∫ v, π.designResidual Q P κ hκ w c v ∂hybridWorldLaw P μ ν) =
        ∫ q, π.potentialGeneratorDrift Q P κ μ w c q
          ∂(hybridWorldLaw P μ ν).prod Model.Instance.uniformClock := by
  have hR := π.retainedDesignResidual_expectation_eq_drift hπ Q P hQ hP μ ν hw hc
  have hD := π.integrable_poissonPotentialDrift hπ Q P hQ κ hκ hI μ ν hw hc
  have hG := π.expected_designResidual_eq_drift hπ Q P hQ hP κ hκ hI μ ν hw hc
  refine ⟨hR.1.sub hD, ?_⟩
  rw [hG, hR.2, ← integral_prod _ hR.1, ← integral_prod _ hD]
  exact (integral_sub hR.1 hD).symm

lemma RandomizedHybridPolicy.expectedDesignResidual_eq_generator (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    π.expectedDesignResidual Q B hμ w c = ∫ q,
      π.rule.potentialGeneratorDrift Q B.individuals (B.intensity.normalize : Measure ℝ) B.intensity w c q
      ∂(B.law π.seedLaw).prod Model.Instance.uniformClock :=
  (π.rule.designResidual_expectation_eq_generator π.measurable_rule Q B.individuals hQ
    (B.individuals.integrable_maximum_of_bounded B.individual_bounded) _ (B.normalizedMark_nonnegative hμ)
      (B.normalizedMark_integrable hμ) B.intensity π.seedLaw hw hc).2

/-- The actual all-policy generator verification bound. -/
theorem RandomizedHybridPolicy.scalarObjective_le_finiteGenerator (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    π.scalarObjective B w c ≤ Model.optimalScalarValue Q w c - ∫ q,
      π.rule.potentialGeneratorDrift Q B.individuals (B.intensity.normalize : Measure ℝ) B.intensity w c q
      ∂(B.law π.seedLaw).prod Model.Instance.uniformClock := by
  have h := π.scalarObjective_le_finitePotential Q hQ B ha hμ hw hc
  rw [π.expectedDesignResidual_eq_generator Q hQ B hμ hw hc] at h
  exact h

/-- The shared finite-potential threshold rule removes all action losses. -/
theorem finitePotentialPolicy_generator_identity (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let π := finitePotentialPolicy Q hQ hw.le hc
    Model.optimalScalarValue Q w c - π.scalarObjective B w c = ∫ q,
      π.rule.potentialGeneratorDrift Q B.individuals (B.intensity.normalize : Measure ℝ) B.intensity w c q
      ∂(B.law π.seedLaw).prod Model.Instance.uniformClock := by
  have h := finitePotentialPolicy_hybrid_residual_identity Q hQ B ha hμ hw hc
  dsimp only at h ⊢
  rw [(finitePotentialPolicy Q hQ hw.le hc).expectedDesignResidual_eq_generator Q hQ B hμ hw hc] at h
  exact h

end ProphetSecretary.Limiting
