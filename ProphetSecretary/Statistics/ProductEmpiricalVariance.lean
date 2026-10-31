import ProphetSecretary.Statistics.TrainingColumns
import ProphetSecretary.Statistics.RowShuffleVariance

/-!
# Variance of a product-empirical expectation

Independent cyclic row shifts express the product-empirical statistic as an
average of ordinary iid block means. Actual shuffle invariance and Jensen
therefore give Var(empirical product expectation) ≤ Var(original statistic)/k.
This proves the variance bound used in `eq:bayes-maximum-variance`; it does
not assert the separate exact Hoeffding component identity.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Classical NNReal
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

lemma empiricalBlockAverage_abs_le {F : (Fin n → ℝ) → ℝ} (C : ℝ≥0)
    (hbound : ∀ x, |F x| ≤ (C : ℝ)) (y : (Fin n × Fin k) → ℝ) :
    |empiricalBlockAverage F y| ≤ C := by
  unfold empiricalBlockAverage
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))]
  calc
    _ ≤ (k : ℝ)⁻¹ * ∑ j : Fin k, |F (fun i => y (i,j))| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
    _ ≤ (k : ℝ)⁻¹ * ∑ _j : Fin k, (C : ℝ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => hbound _) (by positivity)
    _ = C := by
      simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      rw [← mul_assoc,inv_mul_cancel₀ (by exact_mod_cast NeZero.ne k),one_mul]

lemma empiricalProductAverage_eq_rowSymmetrization (F : (Fin n → ℝ) → ℝ) :
    empiricalProductAverage (k := k) F = rowSymmetrization (empiricalBlockAverage (k := k) F) :=
  funext (empiricalProductAverage_eq_integral_shifted_blocks F)

lemma measurable_empiricalProductAverage {F : (Fin n → ℝ) → ℝ} (hF : Measurable F) :
    Measurable (empiricalProductAverage (k := k) F) := by
  rw [empiricalProductAverage_eq_rowSymmetrization]
  exact measurable_rowSymmetrization (measurable_empiricalBlockAverage hF)

lemma empiricalProductAverage_abs_le {F : (Fin n → ℝ) → ℝ} (C : ℝ≥0)
    (hbound : ∀ x, |F x| ≤ (C : ℝ)) (y : (Fin n × Fin k) → ℝ) :
    |empiricalProductAverage F y| ≤ C := by
  rw [empiricalProductAverage_eq_rowSymmetrization]
  exact rowSymmetrization_abs_le (empiricalBlockAverage_abs_le C hbound) y

/-- Exact unbiasedness of the actual product-empirical expectation. -/
theorem integral_empiricalProductAverage (P : Instance n) {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (C : ℝ≥0) (hbound : ∀ x, |F x| ≤ (C : ℝ)) :
    (∫ y, empiricalProductAverage (k := k) F y ∂P.trainingCoordinateLaw k) = ∫ x, F x ∂P.valuesLaw := by
  rw [empiricalProductAverage_eq_rowSymmetrization,
    integral_rowSymmetrization P (measurable_empiricalBlockAverage hF) (empiricalBlockAverage_abs_le C hbound)]
  apply integral_empiricalBlockAverage P hF
  apply Integrable.of_bound hF.aestronglyMeasurable C
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x

/-- Dimension-free variance bound for the actual product-empirical statistic. -/
theorem variance_empiricalProductAverage_le (P : Instance n) {F : (Fin n → ℝ) → ℝ}
    (hF : Measurable F) (C : ℝ≥0) (hbound : ∀ x, |F x| ≤ (C : ℝ)) :
    variance (empiricalProductAverage (k := k) F) (P.trainingCoordinateLaw k) ≤ variance F P.valuesLaw/(k : ℝ) := by
  rw [empiricalProductAverage_eq_rowSymmetrization]
  apply (variance_rowSymmetrization_le P (measurable_empiricalBlockAverage hF) C
    (empiricalBlockAverage_abs_le C hbound)).trans_eq
  apply variance_empiricalBlockAverage P hF
  apply MemLp.of_bound hF.aestronglyMeasurable C
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x

end ProphetSecretary.Statistics
