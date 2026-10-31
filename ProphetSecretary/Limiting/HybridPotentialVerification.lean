import ProphetSecretary.Limiting.HybridDesignResidual

/-!
# Verification by a finite continuation potential

Count-mixture integration of the actual finite Bellman identity bounds every
shared hybrid policy. The common finite-potential threshold rule has equality.
Neither argument optimizes separately after observing the Poisson count.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma FiniteIntensityHybridInstance.normalizedMark_nonnegative (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity ≠ 0) : ∀ᵐ x ∂(B.intensity.normalize : Measure ℝ), 0 ≤ x :=
  (normalized_ae B.intensity hμ B.intensity_supported).mono (fun _ hx => hx.1.le)

noncomputable def RandomizedHybridPolicy.expectedDesignResidual (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) (w c : ℝ) : ℝ :=
  ∫ v, π.rule.designResidual Q B.individuals (B.intensity.normalize : Measure ℝ)
    (B.normalizedMark_nonnegative hμ) w c v ∂B.law π.seedLaw

lemma RandomizedHybridPolicy.hasSum_designResidual_branches (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    HasSum (fun N : ℕ => poissonWeight B.intensity.mass N *
      (π.finiteEvaluation N).expectedReachedTransitionResidual (Q.appendZeros N)
        (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c)
      (π.expectedDesignResidual Q B hμ w c) := by
  let κ : Measure ℝ := B.intensity.normalize
  let hκ := B.normalizedMark_nonnegative hμ
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hI := B.normalizedMark_integrable hμ
  have hm := π.rule.measurable_designResidual π.measurable_rule Q B.individuals hQ hP κ hκ hI hw hc
  have hi := π.rule.integrable_designResidual π.measurable_rule Q B.individuals hQ hP κ hκ hI
    B.intensity π.seedLaw hw hc
  have hs := hasSum_worldLaw_fibers B.intensity (B.individuals.worldLaw π.seedLaw) _ hm hi
  have he (N : ℕ) :
      (∫ v, π.rule.designResidual Q B.individuals κ hκ w c (configurationMk N v.1, v.2)
        ∂(arrayLaw B.intensity N).prod (B.individuals.worldLaw π.seedLaw)) =
      (π.finiteEvaluation N).expectedReachedTransitionResidual (Q.appendZeros N)
        (appendIID B.individuals κ hκ N) w c :=
    π.designResidual_branchIntegral Q B.individuals hQ hP κ hκ hI N hw hc
  convert! hs using 1
  funext N
  rw [he N]

lemma RandomizedHybridPolicy.potential_gap_hasSum (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    HasSum (fun N : ℕ => poissonWeight B.intensity.mass N *
      (Model.optimalScalarValue Q w c -
        (π.finiteEvaluation N).scalarObjective
          (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c -
        (π.finiteEvaluation N).expectedReachedTransitionResidual (Q.appendZeros N)
          (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c))
      (Model.optimalScalarValue Q w c - π.scalarObjective B w c - π.expectedDesignResidual Q B hμ w c) := by
  have hJ := π.hasSum_scalarObjective_branches B ha hμ w c
  have hD := π.hasSum_designResidual_branches Q hQ B hμ hw hc
  have hweight : HasSum (poissonWeight B.intensity.mass) 1 := by convert! hasSum_one_poissonMeasure B.intensity.mass using 1
  have h := ((hweight.mul_right (Model.optimalScalarValue Q w c)).sub hJ).sub hD
  convert! h using 1
  · funext N
    ring
  · simp only [one_mul]

/-- Every competing hybrid policy is bounded by the fixed finite potential
minus its actual expected signed residual. -/
lemma RandomizedHybridPolicy.scalarObjective_le_finitePotential (π : RandomizedHybridPolicy n)
    (Q : Model.Instance n) (hQ : Integrable Model.Instance.maximum Q.valuesLaw)
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    π.scalarObjective B w c ≤ Model.optimalScalarValue Q w c - π.expectedDesignResidual Q B hμ w c := by
  have hs := π.potential_gap_hasSum Q hQ B ha hμ hw hc
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hI := B.normalizedMark_integrable hμ
  have hnn (N : ℕ) : 0 ≤ poissonWeight B.intensity.mass N *
      (Model.optimalScalarValue Q w c -
        (π.finiteEvaluation N).scalarObjective
          (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c -
        (π.finiteEvaluation N).expectedReachedTransitionResidual (Q.appendZeros N)
          (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c) := by
    have hI' : Integrable (fun x : ℝ => x) (B.intensity.normalize : Measure ℝ) := by convert! hI using 1
    have he := hybrid_branch_residual_identity π Q B.individuals hQ hP _ (B.normalizedMark_nonnegative hμ) hI' N hw hc
    have hl := Model.RandomizedPolicy.expectedReachedDesignActionLoss_nonnegative (π.finiteEvaluation N)
      (Q.appendZeros N) (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c
    have hwgt : 0 ≤ poissonWeight B.intensity.mass N := by unfold poissonWeight; positivity
    exact mul_nonneg hwgt (by linarith only [he, hl])
  have h : 0 ≤ Model.optimalScalarValue Q w c - π.scalarObjective B w c - π.expectedDesignResidual Q B hμ w c := by
    rw [← hs.tsum_eq]
    exact tsum_nonneg hnn
  linarith only [h]

/-- The common threshold rule removes all design action losses. -/
lemma finitePotentialPolicy_hybrid_residual_identity (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let π := finitePotentialPolicy Q hQ hw.le hc
    Model.optimalScalarValue Q w c - π.scalarObjective B w c = π.expectedDesignResidual Q B hμ w c := by
  let π := finitePotentialPolicy Q hQ hw.le hc
  have hs := π.potential_gap_hasSum Q hQ B ha hμ hw hc
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hI := B.normalizedMark_integrable hμ
  have he (N : ℕ) : Model.optimalScalarValue Q w c -
      (π.finiteEvaluation N).scalarObjective
        (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c =
      (π.finiteEvaluation N).expectedReachedTransitionResidual (Q.appendZeros N)
        (appendIID B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ) N) w c := by
    have hI' : Integrable (fun x : ℝ => x) (B.intensity.normalize : Measure ℝ) := by convert! hI using 1
    exact finitePotentialPolicy_branch_residual_identity Q B.individuals hQ hP _
      (B.normalizedMark_nonnegative hμ) hI' N hw hc
  have hz : Model.optimalScalarValue Q w c - π.scalarObjective B w c - π.expectedDesignResidual Q B hμ w c = 0 := by
    have hzero := hs.tsum_eq
    simp only [he, sub_self, mul_zero, tsum_zero] at hzero
    exact hzero.symm
  linarith only [hz]

end ProphetSecretary.Limiting
