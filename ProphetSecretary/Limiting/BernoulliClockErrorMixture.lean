import ProphetSecretary.Limiting.HybridClockErrorSum
import ProphetSecretary.Limiting.BernoulliContinuationErrorIntegration

/-!
# Poisson-count averaging of the complete continuation error

The actual configuration count has proved mean λ. Integrable count-branch
transport gives a genuine HasSum, so the original-plus-anonymous occurrence
factor becomes n+λ. This is an analytical mixture, never a count observation
provided to the executed hybrid policy.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- The evaluation law may have arbitrary retained values and zero anonymous
rate. Only the uniform clock marginals and its finite count mean are used. -/
theorem FiniteIntensityHybridInstance.integral_bernoulliClockErrorSum_le
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0) (j : ℕ)
    (R : FiniteIntensityHybridInstance (n+bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j))
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ v, B.clockErrorSum (B.bernoulliApproximation hμ j) w c v ∂R.law ν) ≤
      ((n : ℝ)+(R.intensity.mass : ℝ))*B.bernoulliClockErrorBound w j := by
  let q := bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j
  let Q := B.bernoulliApproximation hμ j
  let D := B.bernoulliClockErrorBound w j
  have hQ : Integrable Model.Instance.maximum Q.valuesLaw :=
    finitePoissonDesign_integrable_maximum B.individuals _ _ _ _
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) (B.normalizedMark_integrable hμ)
  have hG := B.hasSum_clockErrorSum_branches Q hQ R ν hw hc
  let H : HybridWorld (n+q) Seed → ℝ := fun v => ((n : ℝ)+(v.1.1 : ℝ))*D
  have hCountMeas : Measurable (fun v : HybridWorld (n+q) Seed => (v.1.1 : ℝ)) :=
    (measurable_of_countable (fun k : ℕ => (k : ℝ))).comp
      ((configuration_count_measurePreserving R.intensity).measurable.comp measurable_fst)
  have hCountInt : Integrable (fun v : HybridWorld (n+q) Seed => (v.1.1 : ℝ)) (R.law ν) :=
    (measurePreserving_fst (μ := configurationLaw R.intensity) (ν := R.individuals.worldLaw ν)).integrable_comp_of_integrable
      (configuration_count_integrable R.intensity)
  have hHM : Measurable H := (measurable_const.add hCountMeas).mul_const D
  have hHI : Integrable H (R.law ν) := ((integrable_const (n : ℝ)).add hCountInt).mul_const D
  have hH := hasSum_worldLaw_fibers R.intensity (R.individuals.worldLaw ν) H hHM hHI
  have hBranch (N : ℕ) : (∫ v, H (configurationMk N v.1,v.2)
      ∂(arrayLaw R.intensity N).prod (R.individuals.worldLaw ν)) = ((n : ℝ)+(N : ℝ))*D := by
    change (∫ _v, ((n : ℝ)+(N : ℝ))*D ∂(arrayLaw R.intensity N).prod (R.individuals.worldLaw ν)) = _
    simp only [integral_const,probReal_univ,one_smul]
  have hH' : HasSum (fun N : ℕ => poissonWeight R.intensity.mass N*(((n : ℝ)+(N : ℝ))*D))
      (∫ v, H v ∂R.law ν) := by
    convert hH using 1
    · funext N
      rw [hBranch N]
    · rfl
  have hTerm (N : ℕ) : poissonWeight R.intensity.mass N*
      (∫ u : Fin (n+q+N) → ℝ, ∑ k : Fin (n+N), B.finiteDesignContinuationError Q w c u k
        ∂Model.Instance.clocksLaw (n+q+N)) ≤ poissonWeight R.intensity.mass N*(((n : ℝ)+(N : ℝ))*D) := by
    have hWeight : 0 ≤ poissonWeight R.intensity.mass N := by unfold poissonWeight; positivity
    exact mul_le_mul_of_nonneg_left (B.integral_sum_bernoulliContinuationError_le (N := N) ha hμ j hw hc) hWeight
  have hLe := Summable.tsum_le_tsum hTerm hG.summable hH'.summable
  rw [hG.tsum_eq,hH'.tsum_eq] at hLe
  have hCountMean : (∫ v : HybridWorld (n+q) Seed, (v.1.1 : ℝ) ∂R.law ν) = (R.intensity.mass : ℝ) := by
    have hMP := measurePreserving_fst (μ := configurationLaw R.intensity) (ν := R.individuals.worldLaw ν)
    exact (hMP.hasLaw.integral_comp (configuration_count_integrable R.intensity).aestronglyMeasurable).trans
      (configuration_count_expectation R.intensity)
  have hIntegralH : (∫ v, H v ∂R.law ν) = ((n : ℝ)+(R.intensity.mass : ℝ))*D := by
    change (∫ v : HybridWorld (n+q) Seed, ((n : ℝ)+(v.1.1 : ℝ))*D ∂R.law ν) = _
    rw [integral_mul_const,integral_add (integrable_const _) hCountInt,integral_const,hCountMean]
    simp only [probReal_univ,one_smul]
  exact hLe.trans_eq hIntegralH

end ProphetSecretary.Limiting
