import ProphetSecretary.Limiting.HybridDesignActionLoss

/-!
# Exact hybrid performance identity with finite design action loss

The actual law is mixed over its analytical Poisson count. Every branch uses
the adapter of one shared causal policy, without revealing the total count.
The signed potential-generator drift and the nonnegative reached action loss
remain distinct terms in the identity.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma RandomizedHybridPolicy.hasSum_designActionLoss_branches (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    HasSum (fun N : ℕ => poissonWeight B.intensity.mass N*
      (π.finiteEvaluation N).expectedReachedDesignActionLoss (Q.appendZeros N)
        (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c)
      (π.expectedDesignActionLoss Q B w c) := by
  have hMeas := π.rule.measurable_designActionLoss π.measurable_rule Q hQ hw hc
  have hInt := π.rule.integrable_designActionLoss π.measurable_rule Q hQ B π.seedLaw hw hc
  have h := hasSum_worldLaw_fibers B.intensity (B.individuals.worldLaw π.seedLaw) _ hMeas hInt
  have he (N : ℕ) :
      (∫ v, π.rule.designActionLoss Q w c (configurationMk N v.1,v.2)
        ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw π.seedLaw)) =
        (π.finiteEvaluation N).expectedReachedDesignActionLoss (Q.appendZeros N)
          (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c :=
    π.designActionLoss_branchIntegral Q B.individuals hQ _ (B.normalizedMark_nonnegative hμ) N hw hc
  convert h using 1
  · funext N
    rw [he N]
  · rfl

/-- Exact identity for every admissible randomized hybrid competing policy.
The finite design value is distinct from the actual hybrid optimum. -/
theorem RandomizedHybridPolicy.finiteDesign_residualIdentity_split (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Model.optimalScalarValue Q w c-π.scalarObjective B w c =
      π.expectedDesignResidual Q B hμ w c+π.expectedDesignActionLoss Q B w c := by
  have hGap := π.potential_gap_hasSum Q hQ B ha hμ hw hc
  have hLoss := π.hasSum_designActionLoss_branches Q hQ B hμ hw hc
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hI : Integrable (fun x : ℝ => x) (B.intensity.normalize : Measure ℝ) := B.normalizedMark_integrable hμ
  have he (N : ℕ) :
      Model.optimalScalarValue Q w c-
        (π.finiteEvaluation N).scalarObjective
          (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c-
        (π.finiteEvaluation N).expectedReachedTransitionResidual (Q.appendZeros N)
          (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c =
        (π.finiteEvaluation N).expectedReachedDesignActionLoss (Q.appendZeros N)
          (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c := by
    have h := hybrid_branch_residual_identity π Q B.individuals hQ hP _
      (B.normalizedMark_nonnegative hμ) hI N hw hc
    linarith only [h]
  have hGap' : HasSum (fun N : ℕ => poissonWeight B.intensity.mass N*
      (π.finiteEvaluation N).expectedReachedDesignActionLoss (Q.appendZeros N)
        (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c)
      (Model.optimalScalarValue Q w c-π.scalarObjective B w c-π.expectedDesignResidual Q B hμ w c) := by
    convert hGap using 1
    funext N
    rw [he N]
  have hEq := hGap'.unique hLoss
  linarith only [hEq]

/-- The residual term is the actual signed stopped generator drift. The
nonnegative action loss has not been absorbed into an inequality. -/
theorem RandomizedHybridPolicy.finiteDesign_generatorIdentity_split (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Model.optimalScalarValue Q w c-π.scalarObjective B w c =
      (∫ z, π.rule.potentialGeneratorDrift Q B.individuals (B.intensity.normalize : Measure ℝ) B.intensity w c z
        ∂(B.law π.seedLaw).prod Model.Instance.uniformClock)+π.expectedDesignActionLoss Q B w c := by
  have h := π.finiteDesign_residualIdentity_split Q hQ B ha hμ hw hc
  rw [π.expectedDesignResidual_eq_generator Q hQ B hμ hw hc] at h
  exact h

end ProphetSecretary.Limiting
