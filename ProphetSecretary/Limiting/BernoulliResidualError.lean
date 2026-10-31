import ProphetSecretary.Limiting.BernoulliStateError
import ProphetSecretary.Limiting.HybridDesignPerformance

/-!
# Uniform residual error of the finite Bernoulli potential

The signed stopped generator estimate is uniform over every competing policy,
including its independent seed and observed zero identities. The normalized
mark first moment is bounded by the cap before taking the explicit q limit.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

/-- No terminal assumption is needed for this signed residual comparison;
zero terminal is imposed separately in the performance identity. -/
theorem FiniteIntensityHybridInstance.bernoulli_expectedDesignResidual_abs_le
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) (j : ℕ)
    (π : RandomizedHybridPolicy (n+bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j))
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let q := bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j
    |π.expectedDesignResidual (B.bernoulliApproximation hμ j) (B.appendZeroIndividuals q) hμ w c| ≤ B.bernoulliStateError w j := by
  dsimp only
  let rate := (B.intensity : Measure ℝ).real univ
  let q := bernoulliMultiplicity rate j
  let p := bernoulliProbability rate measureReal_nonneg j
  let κ : Measure ℝ := B.intensity.normalize
  let M := ∫ x, x ∂κ
  let C := (Real.pi/2)*w*M*Real.sqrt ((q : ℝ)*(p : ℝ)^2)
  let E := (q : ℝ)*(w*(p : ℝ)^2*M)+C
  let Q := B.bernoulliApproximation hμ j
  let T := B.appendZeroIndividuals q
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  have hI := B.normalizedMark_integrable hμ
  have hQ : Integrable Model.Instance.maximum Q.valuesLaw := finitePoissonDesign_integrable_maximum B.individuals κ
    (B.normalizedMark_nonnegative hμ) p q hP hI
  have hErr := π.rule.bernoulliGenerator_integral_error π.measurable_rule B.individuals κ
    (B.normalizedMark_nonnegative hμ) p hP hI B.intensity
    (bernoulliProbability_total rate measureReal_nonneg j).symm π.seedLaw hw hc
  have hM0 : 0 ≤ M := integral_nonneg_of_ae (B.normalizedMark_nonnegative hμ)
  have hQuad : 0 ≤ (q : ℝ)*(w*(p : ℝ)^2*M) := by positivity
  have hLower : -C ≤ π.expectedDesignResidual Q T hμ w c := by
    rw [π.expectedDesignResidual_eq_generator Q hQ T hμ hw hc]
    exact hErr.2.1
  have hUpper : π.expectedDesignResidual Q T hμ w c ≤ E := by
    rw [π.expectedDesignResidual_eq_generator Q hQ T hμ hw hc]
    exact hErr.2.2
  have hAbs : |π.expectedDesignResidual Q T hμ w c| ≤ E := by
    apply abs_le.mpr
    exact ⟨by dsimp only [E]; linarith only [hLower,hQuad],hUpper⟩
  have hMH : M ≤ (B.cap : ℝ) := by
    have hh := (normalized_ae B.intensity hμ B.intensity_supported).mono fun _ hx => hx.2
    simpa only [id_eq,integral_const,probReal_univ,one_smul] using
      integral_mono_ae hI (integrable_const (B.cap : ℝ)) hh
  have hCoefficient : 0 ≤ w*((q : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((q : ℝ)*(p : ℝ)^2)) := by positivity
  have hCap : E ≤ B.bernoulliStateError w j := by
    calc
      _ = M*(w*((q : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((q : ℝ)*(p : ℝ)^2))) := by dsimp only [E,C]; ring
      _ ≤ (B.cap : ℝ)*(w*((q : ℝ)*(p : ℝ)^2+(Real.pi/2)*Real.sqrt ((q : ℝ)*(p : ℝ)^2))) :=
        mul_le_mul_of_nonneg_right hMH hCoefficient
      _ = _ := by unfold FiniteIntensityHybridInstance.bernoulliStateError; dsimp only [q,p,rate]; ring
  exact hAbs.trans hCap

end ProphetSecretary.Limiting
