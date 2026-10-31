import ProphetSecretary.Limiting.BernoulliGeneratorError
import ProphetSecretary.Limiting.HybridZeroAppendValue

/-!
# Value comparisons before the Poisson approximation limit

The actual uniform generator error bounds all policies in the hybrid model
with virtual zero identities. The finite design optimizer supplies the reverse
comparison, and constructed zero simulation transfers that guarantee to the
unaugmented model. The remaining opposite zero-append embedding is separate.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ}

theorem RandomizedHybridPolicy.scalarObjective_le_BernoulliDesign (π : RandomizedHybridPolicy (n + k))
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    (p : unitInterval) (hrate : (B.intensity : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let κ : Measure ℝ := B.intensity.normalize
    let Q := finitePoissonDesign B.individuals κ (B.normalizedMark_nonnegative hμ) p k
    π.scalarObjective (B.appendZeroIndividuals k) w c ≤ Model.optimalScalarValue Q w c +
      (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) := by
  let κ : Measure ℝ := B.intensity.normalize
  let hκ := B.normalizedMark_nonnegative hμ
  let Q := finitePoissonDesign B.individuals κ hκ p k
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hI := B.normalizedMark_integrable hμ
  have hQ := finitePoissonDesign_integrable_maximum B.individuals κ hκ p k hP hI
  have hver := π.scalarObjective_le_finiteGenerator Q hQ (B.appendZeroIndividuals k) ha hμ hw hc
  have herr := π.rule.bernoulliGenerator_integral_error π.measurable_rule B.individuals κ hκ p hP hI
    B.intensity hrate π.seedLaw hw hc
  change π.scalarObjective (B.appendZeroIndividuals k) w c ≤ Model.optimalScalarValue Q w c -
    (∫ q, π.rule.potentialGeneratorDrift Q (B.individuals.appendZeros k) κ B.intensity w c q
      ∂(hybridWorldLaw (B.individuals.appendZeros k) B.intensity π.seedLaw).prod Model.Instance.uniformClock) at hver
  have hl : -((Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2)) ≤
    (∫ q, π.rule.potentialGeneratorDrift Q (B.individuals.appendZeros k) κ B.intensity w c q
      ∂(hybridWorldLaw (B.individuals.appendZeros k) B.intensity π.seedLaw).prod Model.Instance.uniformClock) := herr.2.1
  change π.scalarObjective (B.appendZeroIndividuals k) w c ≤ _
  linarith only [hver, hl]

/-- Upper comparison for every augmented competing policy. -/
theorem FiniteIntensityHybridInstance.appendZeroValue_le_BernoulliDesign (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) (p : unitInterval)
    (hrate : (B.intensity : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let κ : Measure ℝ := B.intensity.normalize
    let Q := finitePoissonDesign B.individuals κ (B.normalizedMark_nonnegative hμ) p k
    (B.appendZeroIndividuals k).optimalScalarValue w c ≤ Model.optimalScalarValue Q w c +
      (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) := by
  apply csSup_le ((B.appendZeroIndividuals k).scalarPayoffs_nonempty w c)
  rintro _ ⟨π,rfl⟩
  exact π.scalarObjective_le_BernoulliDesign B ha hμ p hrate hw hc

/-- The actual finite-potential optimizer, followed by causal zero simulation,
gives the lower comparison against the unaugmented hybrid value. -/
theorem FiniteIntensityHybridInstance.BernoulliDesignValue_le (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) (p : unitInterval)
    (hrate : (B.intensity : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let κ : Measure ℝ := B.intensity.normalize
    let Q := finitePoissonDesign B.individuals κ (B.normalizedMark_nonnegative hμ) p k
    Model.optimalScalarValue Q w c ≤ B.optimalScalarValue w c +
      (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) +
        (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) := by
  let κ : Measure ℝ := B.intensity.normalize
  let hκ := B.normalizedMark_nonnegative hμ
  let Q := finitePoissonDesign B.individuals κ hκ p k
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hI := B.normalizedMark_integrable hμ
  have hQ := finitePoissonDesign_integrable_maximum B.individuals κ hκ p k hP hI
  let π := finitePotentialPolicy Q hQ hw.le hc
  have heq := finitePotentialPolicy_generator_identity Q hQ (B.appendZeroIndividuals k) ha hμ hw hc
  have herr := π.rule.bernoulliGenerator_integral_error π.measurable_rule B.individuals κ hκ p hP hI
    B.intensity hrate π.seedLaw hw hc
  have hval := ((B.appendZeroIndividuals k).scalarObjective_le_value π w c).trans
    (B.value_appendZeroIndividuals_le k ha hw.le hc)
  change Model.optimalScalarValue Q w c - π.scalarObjective (B.appendZeroIndividuals k) w c =
    (∫ q, π.rule.potentialGeneratorDrift Q (B.individuals.appendZeros k) κ B.intensity w c q
      ∂(hybridWorldLaw (B.individuals.appendZeros k) B.intensity π.seedLaw).prod Model.Instance.uniformClock) at heq
  have hu : (∫ q, π.rule.potentialGeneratorDrift Q (B.individuals.appendZeros k) κ B.intensity w c q
      ∂(hybridWorldLaw (B.individuals.appendZeros k) B.intensity π.seedLaw).prod Model.Instance.uniformClock) ≤
    (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) +
      (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) := herr.2.2
  change Model.optimalScalarValue Q w c ≤ _
  linarith only [heq, hu, hval]

/-- Zero-identity value invariance discharges the unaugmented upper comparison. -/
theorem FiniteIntensityHybridInstance.value_le_BernoulliDesign (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) (p : unitInterval)
    (hrate : (B.intensity : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let κ : Measure ℝ := B.intensity.normalize
    let Q := finitePoissonDesign B.individuals κ (B.normalizedMark_nonnegative hμ) p k
    B.optimalScalarValue w c ≤ Model.optimalScalarValue Q w c +
      (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) := by
  have h := B.appendZeroValue_le_BernoulliDesign ha hμ p hrate hw hc
  dsimp only at h ⊢
  rw [B.value_appendZeroIndividuals k ha hw.le hc] at h
  exact h

/-- Two-sided finite approximation with all errors and dependencies explicit.
The normalized mark law may have arbitrary support inside the common cap. -/
theorem FiniteIntensityHybridInstance.BernoulliDesignValue_abs_difference_le (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) (p : unitInterval)
    (hrate : (B.intensity : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let κ : Measure ℝ := B.intensity.normalize
    let Q := finitePoissonDesign B.individuals κ (B.normalizedMark_nonnegative hμ) p k
    |Model.optimalScalarValue Q w c - B.optimalScalarValue w c| ≤
      (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) +
        (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) := by
  have hU := B.BernoulliDesignValue_le ha hμ p hrate hw hc
  have hL := B.value_le_BernoulliDesign ha hμ p hrate hw hc
  dsimp only at hU hL ⊢
  have hnn : 0 ≤ (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂(B.intensity.normalize : Measure ℝ)) :=
    mul_nonneg (Nat.cast_nonneg k) (mul_nonneg (mul_nonneg hw.le (sq_nonneg _))
      (integral_nonneg_of_ae (B.normalizedMark_nonnegative hμ)))
  rw [abs_le]
  constructor <;> linarith only [hU,hL,hnn]

end ProphetSecretary.Limiting
