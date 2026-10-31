import ProphetSecretary.Limiting.RareGeneratorError
import ProphetSecretary.Limiting.FiniteResidualTransport
import ProphetSecretary.Model.ValueResidualComparison

/-!
# Original finite values compared with rare Bernoulli potentials

The derived actual-generator bounds transfer to every admissible finite policy
through its anonymous-ignoring adapter. The finite Bellman identity supplies
both value comparisons, and actual zero simulation removes the virtual zeros.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n m k : ℕ}

theorem rare_finiteResidual_bounds (P : Model.Instance n) (R : Model.Instance m)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hR : Integrable Model.Instance.maximum R.valuesLaw)
    {H w c : ℝ} (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ x ∂R.law i, x ≤ H) (hw : 0 < w) (hc : 0 ≤ c)
    (p : unitInterval) (hrate : (positiveOfferIntensity R : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    (hκ : ∀ᵐ x ∂((positiveOfferIntensity R).normalize : Measure ℝ), 0 ≤ x)
    (hI : Integrable id ((positiveOfferIntensity R).normalize : Measure ℝ)) :
    let κ : Measure ℝ := (positiveOfferIntensity R).normalize
    let Q := rarePoissonDesign P κ hκ p m k
    let A := (P.appendIndependent R).appendZeros k
    let C := (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2)
    let D := (Real.pi / 2) * w * H * Real.sqrt (∑ i, distributionTail R 0 i ^ 2)
    ∀ π : Model.RandomizedPolicy (n + m + k),
      -(C + D) ≤ π.expectedReachedTransitionResidual Q A w c ∧
        π.expectedReachedTransitionResidual Q A w c ≤ (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) + C + D := by
  let κ : Measure ℝ := (positiveOfferIntensity R).normalize
  let Q := rarePoissonDesign P κ hκ p m k
  let A := (P.appendIndependent R).appendZeros k
  have hQ := rarePoissonDesign_integrable_maximum P κ hκ p m k hP hI
  have hA := (P.appendIndependent R).appendZeros_integrable_maximum k (P.appendIndependent_integrable_maximum R hP hR)
  dsimp only
  intro π
  letI : IsProbabilityMeasure π.seedLaw := π.probability
  let ψ : HybridRule (n + m + k) π.Seed := (ignorePoisson π).rule
  have hψ : ψ.IsMeasurable := (ignorePoisson π).measurable_rule
  have h := ψ.rare_retainedGenerator_integral_error hψ
    P R hP hR hH hcap hw hc p hrate hκ hI 0 π.seedLaw
  have hi : Integrable (ψ.retainedPotentialDrift Q A w c)
      ((hybridWorldLaw A 0 π.seedLaw).prod Model.Instance.uniformClock) := h.1
  have he := finite_reachedResidual_eq_hybridDrift π Q A hQ hA 0 hw hc
  have he' : π.expectedReachedTransitionResidual Q A w c =
      ∫ q, ψ.retainedPotentialDrift Q A w c q
        ∂(hybridWorldLaw A 0 π.seedLaw).prod Model.Instance.uniformClock :=
    he.trans (integral_prod _ hi).symm
  change _ ≤ π.expectedReachedTransitionResidual Q A w c ∧ π.expectedReachedTransitionResidual Q A w c ≤ _
  rw [he']
  exact ⟨h.2.1,h.2.2⟩

/-- Uniform finite value error before the virtual approximation limit. -/
theorem rare_finiteValue_abs_difference_le (P : Model.Instance n) (R : Model.Instance m)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hR : Integrable Model.Instance.maximum R.valuesLaw)
    {H w c : ℝ} (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ x ∂R.law i, x ≤ H) (hw : 0 < w) (hc : 0 ≤ c)
    (p : unitInterval) (hrate : (positiveOfferIntensity R : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    (hκ : ∀ᵐ x ∂((positiveOfferIntensity R).normalize : Measure ℝ), 0 ≤ x)
    (hI : Integrable id ((positiveOfferIntensity R).normalize : Measure ℝ)) :
    let κ : Measure ℝ := (positiveOfferIntensity R).normalize
    let Q := rarePoissonDesign P κ hκ p m k
    |Model.optimalScalarValue Q w c - Model.optimalScalarValue (P.appendIndependent R) w c| ≤
      (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) +
        (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) +
          (Real.pi / 2) * w * H * Real.sqrt (∑ i, distributionTail R 0 i ^ 2) := by
  let κ : Measure ℝ := (positiveOfferIntensity R).normalize
  let Q := rarePoissonDesign P κ hκ p m k
  have hS := P.appendIndependent_integrable_maximum R hP hR
  have hA := (P.appendIndependent R).appendZeros_integrable_maximum k hS
  have hQ := rarePoissonDesign_integrable_maximum P κ hκ p m k hP hI
  have h := Model.optimalScalarValue_comparison_of_residual_bounds Q ((P.appendIndependent R).appendZeros k)
    hQ hA hw hc (rare_finiteResidual_bounds P R hP hR hH hcap hw hc p hrate hκ hI)
  rw [(P.appendIndependent R).optimalScalarValue_appendZeros k hS hw.le hc] at h
  have hnn : 0 ≤ (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) :=
    mul_nonneg (Nat.cast_nonneg _) (mul_nonneg (mul_nonneg hw.le (sq_nonneg _)) (integral_nonneg_of_ae hκ))
  change |Model.optimalScalarValue Q w c - Model.optimalScalarValue (P.appendIndependent R) w c| ≤ _
  rw [abs_le]
  constructor <;> linarith only [h.1,h.2,hnn]

end ProphetSecretary.Limiting
