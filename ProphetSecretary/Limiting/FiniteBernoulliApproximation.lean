import ProphetSecretary.Limiting.BernoulliScale

/-!
# Actual finite approximation of a finite-intensity hybrid value

The retained distributions and the normalized mark law are fixed. Only the
virtual multiplicity grows, with total positive intensity exactly preserved on
every approximation. The quantitative value comparison proves convergence;
no convergence of policies, score expectations, or derivatives is asserted here.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Limiting

variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.bernoulliApproximation
    (B : FiniteIntensityHybridInstance n) (hμ : B.intensity ≠ 0) (m : ℕ) :
    Model.Instance (n + bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) m) :=
  finitePoissonDesign B.individuals (B.intensity.normalize : Measure ℝ) (B.normalizedMark_nonnegative hμ)
    (bernoulliProbability ((B.intensity : Measure ℝ).real univ) measureReal_nonneg m)
    (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) m)

theorem FiniteIntensityHybridInstance.bernoulliApproximation_value_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Tendsto (fun m => Model.optimalScalarValue (B.bernoulliApproximation hμ m) w c)
      atTop (𝓝 (B.optimalScalarValue w c)) := by
  let rate := (B.intensity : Measure ℝ).real univ
  let M := ∫ x, x ∂(B.intensity.normalize : Measure ℝ)
  let err : ℕ → ℝ := fun m =>
    (bernoulliMultiplicity rate m : ℝ) * (w * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2 * M) +
      (Real.pi / 2) * w * M * Real.sqrt ((bernoulliMultiplicity rate m : ℝ) *
        (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2)
  have hbound (m : ℕ) : |Model.optimalScalarValue (B.bernoulliApproximation hμ m) w c - B.optimalScalarValue w c| ≤ err m := by
    exact B.BernoulliDesignValue_abs_difference_le ha hμ (bernoulliProbability rate measureReal_nonneg m)
      (bernoulliProbability_total rate measureReal_nonneg m).symm hw hc
  have herr : Tendsto err atTop (𝓝 0) := bernoulliProbability_error_tendsto_zero rate measureReal_nonneg w M
  have hnorm : Tendsto (fun m => ‖Model.optimalScalarValue (B.bernoulliApproximation hμ m) w c - B.optimalScalarValue w c‖)
      atTop (𝓝 0) := by
    apply squeeze_zero (fun _ => norm_nonneg _) _ herr
    intro m
    simpa only [Real.norm_eq_abs] using hbound m
  exact tendsto_iff_norm_sub_tendsto_zero.mpr hnorm

/-- Uniformity over every duration weight and a bounded positive reward-weight
interval follows directly from the explicit approximation error. -/
theorem FiniteIntensityHybridInstance.bernoulliApproximation_value_uniform
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hμ : B.intensity ≠ 0)
    {W ε : ℝ} (_hW : 0 ≤ W) (hε : 0 < ε) :
    ∀ᶠ m in atTop, ∀ w c : ℝ, 0 < w → w ≤ W → 0 ≤ c →
      |Model.optimalScalarValue (B.bernoulliApproximation hμ m) w c - B.optimalScalarValue w c| < ε := by
  let rate := (B.intensity : Measure ℝ).real univ
  let M := ∫ x, x ∂(B.intensity.normalize : Measure ℝ)
  have hM : 0 ≤ M := integral_nonneg_of_ae (B.normalizedMark_nonnegative hμ)
  have hErr := bernoulliProbability_error_tendsto_zero rate measureReal_nonneg W M
  have hevent := (tendsto_order.mp hErr).2 ε hε
  filter_upwards [hevent] with m hm
  intro w c hw hwW hc
  have hbound := B.BernoulliDesignValue_abs_difference_le ha hμ (bernoulliProbability rate measureReal_nonneg m)
    (bernoulliProbability_total rate measureReal_nonneg m).symm hw hc
  have hweight :
      (bernoulliMultiplicity rate m : ℝ) * (w * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2 * M) +
        (Real.pi / 2) * w * M * Real.sqrt ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2) ≤
      (bernoulliMultiplicity rate m : ℝ) * (W * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2 * M) +
        (Real.pi / 2) * W * M * Real.sqrt ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2) := by
    have hC : 0 ≤ M * ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2 +
        (Real.pi / 2) * Real.sqrt ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2)) := by positivity
    calc
      _ = w * (M * ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2 +
        (Real.pi / 2) * Real.sqrt ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2))) := by ring
      _ ≤ W * (M * ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2 +
        (Real.pi / 2) * Real.sqrt ((bernoulliMultiplicity rate m : ℝ) * (bernoulliProbability rate measureReal_nonneg m : ℝ) ^ 2))) :=
          mul_le_mul_of_nonneg_right hwW hC
      _ = _ := by ring
  exact (hbound.trans hweight).trans_lt hm

end ProphetSecretary.Limiting
