import ProphetSecretary.Model.TrainingLaw

/-!
# Product empirical laws

The empirical distribution uses all observations of one marginal. It is a finite atomic
law because a training sample is finite; the original instance remains unrestricted.
-/

open MeasureTheory
open scoped BigOperators ENNReal

namespace ProphetSecretary.Model

/-- Empirical law of `k` observations. Probability statements require `k≠0`. -/
noncomputable def empiricalLaw {k : ℕ} (y : Fin k → ℝ) : Measure ℝ :=
  (k : ℝ≥0∞)⁻¹ • ∑ j : Fin k, Measure.dirac (y j)

instance empiricalLaw_probability {k : ℕ} [NeZero k] (y : Fin k → ℝ) :
    IsProbabilityMeasure (empiricalLaw y) := by
  constructor
  simp only [empiricalLaw, Measure.smul_apply]
  simp
  exact ENNReal.inv_mul_cancel (a := (k : ℝ≥0∞)) (by exact_mod_cast (NeZero.ne k)) (by simp)

lemma integrable_empiricalLaw {k : ℕ} [NeZero k] (y : Fin k → ℝ) (f : ℝ → ℝ) :
    Integrable f (empiricalLaw y) := by
  apply Integrable.smul_measure
  · apply integrable_finsetSum_measure.mpr
    intro j _
    exact integrable_dirac (by simp)
  · simp [NeZero.ne k]

/-- Averages under the empirical law are exactly sample averages. -/
lemma integral_empiricalLaw {k : ℕ} [NeZero k] (y : Fin k → ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂empiricalLaw y) = (k : ℝ)⁻¹ * ∑ j, f (y j) := by
  rw [empiricalLaw, integral_smul_measure]
  have hsum : (∫ x, f x ∂∑ j : Fin k, Measure.dirac (y j)) = ∑ j, f (y j) := by
    rw [integral_finsetSum_measure (fun _ _ => integrable_dirac (by simp))]
    simp
  rw [hsum]
  simp

/-- Nonnegative observations induce a nonnegative empirical law. -/
lemma empiricalLaw_nonnegative {k : ℕ} (y : Fin k → ℝ) (hy : ∀ j, 0 ≤ y j) :
    ∀ᵐ x ∂empiricalLaw y, 0 ≤ x := by
  apply Measure.ae_smul_measure
  apply ae_finsetSum_measure_iff.mpr
  intro j _
  simpa using hy j

/-- The product of the empirical marginals. -/
noncomputable def empiricalInstance {n k : ℕ} [NeZero k] (y : Reservoir n k)
    (hy : ∀ i j, 0 ≤ y i j) : Instance n where
  law i := empiricalLaw (y i)
  probability _ := inferInstance
  nonnegative i := empiricalLaw_nonnegative (y i) (hy i)

lemma empiricalInstance_integrable {n k : ℕ} [NeZero k] (y : Reservoir n k)
    (hy : ∀ i j, 0 ≤ y i j) :
    Integrable Instance.maximum (empiricalInstance y hy).valuesLaw := by
  apply Instance.integrable_maximum
  intro i
  exact integrable_empiricalLaw (y i) id

end ProphetSecretary.Model
