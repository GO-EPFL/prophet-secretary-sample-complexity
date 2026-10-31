import ProphetSecretary.Limiting.HybridFirstMomentBound
import ProphetSecretary.Limiting.ZeroIntensity

/-!
# Hybrid value and the anonymous first moment

The normalized mark law is used only to construct the actual Poisson process.
The final bound uses the intensity's unnormalized first moment, including the
zero-intensity boundary and zero expected maxima of retained instances.
-/

open MeasureTheory Set
open scoped ENNReal

namespace ProphetSecretary.Limiting

lemma integral_finiteIntensity_eq_mass_normalized (μ : FiniteMeasure ℝ) :
    (∫ x, x ∂(μ : Measure ℝ)) = (μ.mass : ℝ) * ∫ x, x ∂(μ.normalize : Measure ℝ) := by
  have hm : (μ : Measure ℝ) = (μ.mass : ℝ≥0∞) • (μ.normalize : Measure ℝ) :=
    congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) μ.self_eq_mass_smul_normalize
  rw [hm, integral_smul_measure]
  rfl

variable {n : ℕ}

lemma FiniteIntensityHybridInstance.value_gap_le_intensity_firstMoment (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    0 ≤ B.optimalScalarValue w c - Model.optimalScalarValue B.individuals w c ∧
      B.optimalScalarValue w c - Model.optimalScalarValue B.individuals w c ≤
        w * ∫ x, x ∂(B.intensity : Measure ℝ) := by
  refine ⟨sub_nonneg.mpr (B.finiteValue_le ha w c), ?_⟩
  by_cases hμ : B.intensity = 0
  · rw [B.value_zero_intensity ha hμ hw.le hc, sub_self, hμ]
    simp
  · have hu := B.value_le_finiteValue_add_firstMoment ha hμ hw hc
    rw [integral_finiteIntensity_eq_mass_normalized]
    nlinarith only [hu]

end ProphetSecretary.Limiting
