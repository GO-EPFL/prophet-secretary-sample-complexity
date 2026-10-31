import ProphetSecretary.Statistics.RemainingSize
import ProphetSecretary.Model.TrainingCoordinates
import ProphetSecretary.Model.EmpiricalTotalization

/-!
# Actual empirical first moments are unbiased

The total empirical instance uses max(0,sample) on every training outcome.
Nonnegativity of the original marginal makes this totalization invisible
almost surely. The resulting exact expectation is used for the tiny-offer
case of `upstat:tiny`, without a data-selected-weight centering assertion.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma empirical_coordinate_firstMoment_eq (i : Fin n) (y : (Fin n × Fin k) → ℝ) :
    (∫ x, x ∂(totalEmpiricalInstance (reservoirCoordinates.symm y)).law i) =
      (k : ℝ)⁻¹ * ∑ j, max 0 (y (i,j)) := by
  exact integral_empiricalLaw (fun j => max 0 (y (i,j))) id

lemma Instance.integrable_empirical_coordinate_firstMoment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) :
    Integrable (fun y : (Fin n × Fin k) → ℝ =>
      ∫ x, x ∂(totalEmpiricalInstance (reservoirCoordinates.symm y)).law i) (P.trainingCoordinateLaw k) := by
  have hXi : Integrable (fun x : ℝ => max 0 x) (P.law i) :=
    (P.integrable_maximum_iff.mp hP i).congr
      ((P.nonnegative i).mono fun _ hx => (max_eq_right hx).symm)
  have hrow (j : Fin k) : Integrable (fun y : (Fin n × Fin k) → ℝ => max 0 (y (i,j)))
      (P.trainingCoordinateLaw k) := by
    have hp : MeasurePreserving (fun y : (Fin n × Fin k) → ℝ => y (i,j))
        (P.trainingCoordinateLaw k) (P.law i) :=
      measurePreserving_eval (fun p : Fin n × Fin k => P.law p.1) (i,j)
    exact hp.integrable_comp_of_integrable hXi
  have heq : (fun y : (Fin n × Fin k) → ℝ =>
      ∫ x, x ∂(totalEmpiricalInstance (reservoirCoordinates.symm y)).law i) =
      fun y => (k : ℝ)⁻¹ * ∑ j, max 0 (y (i,j)) := funext fun y => empirical_coordinate_firstMoment_eq i y
  rw [heq]
  exact (integrable_finsetSum _ (fun j _ => hrow j)).const_mul _

/-- The actual product training law, rather than an assumed unbiased estimator. -/
theorem Instance.integral_empirical_coordinate_firstMoment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) :
    (∫ y : (Fin n × Fin k) → ℝ,
      (∫ x, x ∂(totalEmpiricalInstance (reservoirCoordinates.symm y)).law i) ∂P.trainingCoordinateLaw k) =
      ∫ x, x ∂P.law i := by
  have hXi : Integrable (fun x : ℝ => max 0 x) (P.law i) :=
    (P.integrable_maximum_iff.mp hP i).congr
      ((P.nonnegative i).mono fun _ hx => (max_eq_right hx).symm)
  have hrow (j : Fin k) : Integrable (fun y : (Fin n × Fin k) → ℝ => max 0 (y (i,j)))
      (P.trainingCoordinateLaw k) :=
    (measurePreserving_eval (fun p : Fin n × Fin k => P.law p.1) (i,j)).integrable_comp_of_integrable hXi
  have hmean (j : Fin k) : (∫ y : (Fin n × Fin k) → ℝ, max 0 (y (i,j)) ∂P.trainingCoordinateLaw k) =
      ∫ x, x ∂P.law i := by
    have hp : MeasurePreserving (fun y : (Fin n × Fin k) → ℝ => y (i,j))
        (P.trainingCoordinateLaw k) (P.law i) :=
      measurePreserving_eval (fun p : Fin n × Fin k => P.law p.1) (i,j)
    have hfm : Measurable (fun x : ℝ => max 0 x) := measurable_const.max measurable_id
    have heq := integral_map (μ := P.trainingCoordinateLaw k) hp.measurable.aemeasurable hfm.aestronglyMeasurable
    rw [hp.map_eq] at heq
    have hnn : (∫ x, max 0 x ∂P.law i) = ∫ x, x ∂P.law i :=
      integral_congr_ae ((P.nonnegative i).mono fun _ hx => max_eq_right hx)
    exact heq.symm.trans hnn
  simp_rw [empirical_coordinate_firstMoment_eq]
  rw [integral_const_mul, integral_finsetSum _ (fun j _ => hrow j)]
  simp only [hmean, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hk : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne k)
  rw [← mul_assoc, inv_mul_cancel₀ hk, one_mul]

lemma Instance.integrable_empirical_totalFirstMoment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    Integrable (fun y : (Fin n × Fin k) → ℝ =>
      (totalEmpiricalInstance (reservoirCoordinates.symm y)).totalFirstMoment) (P.trainingCoordinateLaw k) := by
  change Integrable (fun y => ∑ i, ∫ x, x ∂(totalEmpiricalInstance (reservoirCoordinates.symm y)).law i) _
  exact integrable_finsetSum _ (fun i _ => P.integrable_empirical_coordinate_firstMoment hP i)

lemma Instance.integral_empirical_totalFirstMoment (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    (∫ y : (Fin n × Fin k) → ℝ,
      (totalEmpiricalInstance (reservoirCoordinates.symm y)).totalFirstMoment ∂P.trainingCoordinateLaw k) =
      P.totalFirstMoment := by
  change (∫ y : (Fin n × Fin k) → ℝ,
    ∑ i, ∫ x, x ∂(totalEmpiricalInstance (reservoirCoordinates.symm y)).law i ∂P.trainingCoordinateLaw k) = _
  rw [integral_finsetSum _ (fun i _ => P.integrable_empirical_coordinate_firstMoment hP i)]
  simp_rw [P.integral_empirical_coordinate_firstMoment hP]
  rfl

end ProphetSecretary.Model
