import ProphetSecretary.Limiting.RareMarginalNormalization

/-!
# Positive rescaling preserves the analytical normalized mark law

The finite intensity is scaled; its normalized mark distribution is used only
analytically. The zero-intensity fallback is treated explicitly.
-/
open MeasureTheory Set
open scoped NNReal Classical
namespace ProphetSecretary.Limiting

lemma finiteMeasure_mass_smul (r : ℝ≥0) (μ : FiniteMeasure ℝ) : (r • μ).mass = r*μ.mass := by
  change (r • μ) univ = r*μ univ
  rw [FiniteMeasure.smul_apply,smul_eq_mul]

lemma normalizedMarkOrZero_smul (μ : FiniteMeasure ℝ) {r : ℝ≥0} (hr : 0 < r) :
    normalizedMarkOrZero (r • μ) = normalizedMarkOrZero μ := by
  by_cases hμ : μ = 0
  · simp [hμ]
  have hm : μ.mass ≠ 0 := μ.mass_nonzero_iff.mpr hμ
  have hs : r • μ ≠ 0 := by
    rw [← FiniteMeasure.mass_nonzero_iff,finiteMeasure_mass_smul]
    exact mul_ne_zero (ne_of_gt hr) hm
  rw [normalizedMarkOrZero,if_neg hs,normalizedMarkOrZero,if_neg hμ,
    (r • μ).toMeasure_normalize_eq_of_nonzero hs,μ.toMeasure_normalize_eq_of_nonzero hμ,
    finiteMeasure_mass_smul,FiniteMeasure.toMeasure_smul,smul_smul]
  congr 1
  field_simp [ne_of_gt hr,hm]

end ProphetSecretary.Limiting
