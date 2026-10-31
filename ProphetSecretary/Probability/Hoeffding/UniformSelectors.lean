import ProphetSecretary.Model.EmpiricalMomentsMeasurability

/-!
# Actual finite uniform sample-selector averages

The independent empirical index law assigns every selector the mass k^(-r).
Its integral is therefore the normalized finite sum, including the empty
coordinate family. The normalization is proved from the actual product law.
-/
open MeasureTheory Set
open scoped Classical BigOperators ENNReal
namespace ProphetSecretary.Probability.Hoeffding
open ProphetSecretary.Model
variable {I : Type*} [Fintype I] {k : ℕ} [NeZero k]

omit [NeZero k] in
lemma empiricalIndexLaw_singleton (j : Fin k) : empiricalIndexLaw k {j} = (k : ℝ≥0∞)⁻¹ := by
  simp [empiricalIndexLaw,Measure.smul_apply]

lemma selectorLaw_singleton (a : I → Fin k) :
    (Measure.pi (fun _ : I => empiricalIndexLaw k)).real {a} = ((k : ℝ)^Fintype.card I)⁻¹ := by
  unfold Measure.real
  rw [Measure.pi_singleton]
  simp_rw [empiricalIndexLaw_singleton]
  simp

lemma integral_uniform_selectors (F : (I → Fin k) → ℝ) :
    (∫ a, F a ∂Measure.pi (fun _ : I => empiricalIndexLaw k)) =
      ((k : ℝ)^Fintype.card I)⁻¹ * ∑ a : I → Fin k, F a := by
  rw [integral_fintype Integrable.of_finite]
  simp_rw [selectorLaw_singleton,smul_eq_mul]
  rw [Finset.mul_sum]

lemma integral_uniform_index (F : Fin k → ℝ) :
    (∫ r, F r ∂empiricalIndexLaw k) = (k : ℝ)⁻¹ * ∑ r : Fin k, F r := by
  rw [integral_fintype Integrable.of_finite]
  simp only [Measure.real,empiricalIndexLaw_singleton,ENNReal.toReal_inv,ENNReal.toReal_natCast,smul_eq_mul]
  rw [Finset.mul_sum]

end ProphetSecretary.Probability.Hoeffding
