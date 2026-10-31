import ProphetSecretary.Limiting.RareFiniteValueComparison
import ProphetSecretary.Limiting.PoissonizedFamily
import ProphetSecretary.Limiting.ZeroPositiveIntensity

/-!
# Sharp causal comparison at zero terminal reward

A common finite Bernoulli potential compares both original and Poisson laws.
The original rare-offer error has the manuscript's sharp π/2 coefficient;
all virtual approximation errors vanish along the explicit rare-probability
sequence. Both sides optimize over the full admissible policy classes.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators

namespace ProphetSecretary.Limiting

variable {n m : ℕ}

/-- The core of `lem:causal-poisson` for nonzero positive intensity and zero
terminal reward, with retained/replaced identities displayed as two blocks. -/
theorem causalPoisson_zeroTerminal_nonzeroIntensity (P : Model.Instance n) (R : Model.Instance m)
    (H : ℝ≥0) (hPcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hRcap : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) (hμ : positiveOfferIntensity R ≠ 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    |Model.optimalScalarValue (P.appendIndependent R) w c - (poissonizedFamily P R H hPcap hRcap).optimalScalarValue w c| ≤
      (Real.pi / 2) * w * (H : ℝ) * Real.sqrt (∑ i, distributionTail R 0 i ^ 2) := by
  let B := poissonizedFamily P R H hPcap hRcap
  let rate := (positiveOfferIntensity R : Measure ℝ).real univ
  have hrate : 0 ≤ rate := measureReal_nonneg
  let κ : Measure ℝ := (positiveOfferIntensity R).normalize
  let hκ := B.normalizedMark_nonnegative hμ
  have hI := B.normalizedMark_integrable hμ
  let K := fun j : ℕ => bernoulliMultiplicity rate j
  let p := fun j : ℕ => bernoulliProbability rate hrate j
  let Q := fun j : ℕ => rarePoissonDesign P κ hκ (p j) m (K j)
  let M := ∫ x, x ∂κ
  let E := fun j : ℕ => (K j : ℝ) * (w * (p j : ℝ) ^ 2 * M) +
    (Real.pi / 2) * w * M * Real.sqrt ((K j : ℝ) * (p j : ℝ) ^ 2)
  let D := (Real.pi / 2) * w * (H : ℝ) * Real.sqrt (∑ i, distributionTail R 0 i ^ 2)
  have hP := P.integrable_maximum_of_bounded hPcap
  have hR := R.integrable_maximum_of_bounded hRcap
  have hV : Tendsto (fun j => Model.optimalScalarValue (Q j) w c) atTop (𝓝 (B.optimalScalarValue w c)) := by
    have h := (B.appendZeroIndividuals m).bernoulliApproximation_value_tendsto (by rfl) hμ hw hc
    rw [B.value_appendZeroIndividuals m (by rfl) hw.le hc] at h
    exact h
  have hE : Tendsto E atTop (𝓝 0) := bernoulliProbability_error_tendsto_zero rate hrate w M
  have hbound (j : ℕ) :
      |Model.optimalScalarValue (Q j) w c - Model.optimalScalarValue (P.appendIndependent R) w c| ≤ E j + D := by
    exact rare_finiteValue_abs_difference_le P R hP hR H.coe_nonneg hRcap hw hc (p j)
      (bernoulliProbability_total rate hrate j).symm hκ hI
  have hleft := (hV.sub_const (Model.optimalScalarValue (P.appendIndependent R) w c)).abs
  have hright : Tendsto (fun j => E j + D) atTop (𝓝 D) := by
    simpa only [zero_add] using hE.add_const D
  have h := le_of_tendsto_of_tendsto hleft hright (Filter.Eventually.of_forall hbound)
  change |Model.optimalScalarValue (P.appendIndependent R) w c - B.optimalScalarValue w c| ≤ D
  exact (abs_sub_comm _ _).le.trans h

lemma FiniteIntensityHybridInstance.value_zero_rewardWeight (B : FiniteIntensityHybridInstance n)
    {c : ℝ} (hc : 0 ≤ c) : B.optimalScalarValue 0 c = c := by
  apply le_antisymm
  · simpa only [zero_mul, zero_add] using B.optimalScalarValue_le (w := 0) le_rfl hc
  · exact B.durationReward_le_optimalScalarValue (w := 0) le_rfl

/-- `lem:causal-poisson` at zero terminal reward for an arbitrary retained
block and replaced block, including zero intensity and zero reward weight.
The general-reserve and arbitrary-original-label transfers are separate. -/
theorem causalPoisson_zeroTerminal (P : Model.Instance n) (R : Model.Instance m)
    (H : ℝ≥0) (hPcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hRcap : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    |Model.optimalScalarValue (P.appendIndependent R) w c - (poissonizedFamily P R H hPcap hRcap).optimalScalarValue w c| ≤
      (Real.pi / 2) * w * (H : ℝ) * Real.sqrt (∑ i, distributionTail R 0 i ^ 2) := by
  by_cases hw0 : w = 0
  · subst w
    rw [Model.optimalScalarValue_zero_rewardWeight (P.appendIndependent R) hc,
      (poissonizedFamily P R H hPcap hRcap).value_zero_rewardWeight hc, sub_self, abs_zero]
    simp only [mul_zero, zero_mul, le_refl]
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    by_cases hμ : positiveOfferIntensity R = 0
    · rw [causalPoisson_zeroTerminal_zeroIntensity P R H hPcap hRcap hμ hw hc, sub_self, abs_zero]
      positivity
    · exact causalPoisson_zeroTerminal_nonzeroIntensity P R H hPcap hRcap hμ hwpos hc

end ProphetSecretary.Limiting
