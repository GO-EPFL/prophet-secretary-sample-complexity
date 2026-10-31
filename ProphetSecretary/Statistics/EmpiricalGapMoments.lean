import ProphetSecretary.Model.UnitScalarGap
import ProphetSecretary.Model.EmpiricalValueMeasurability
import ProphetSecretary.Statistics.EmpiricalMaximumVariance

/-! # Measurability and unit integrability of fixed-weight empirical gaps -/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma measurable_empiricalNormalizedGap {a : ℝ} (ha : a∈Ioc (0 : ℝ) 1) :
    Measurable (fun y : (Fin n × Fin k) → ℝ =>
      normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a) := by
  have hV := measurable_optimalScalarValue_totalEmpirical
    (y := fun y : (Fin n × Fin k) → ℝ => reservoirCoordinates.symm y)
    (w := fun _ => a) (c := fun _ => 1-a)
    (fun i j => measurable_pi_apply (i,j)) measurable_const measurable_const
    (fun _ => ha.1) (fun _ => sub_nonneg.mpr ha.2)
  exact hV.sub (((measurable_empiricalExpectedMaximum.const_mul a).add_const (1-a)).const_mul
    optimalCompetitiveRatio)

lemma Instance.empiricalNormalizedGap_mem_unit_ae (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {a : ℝ} (ha : a∈Icc (0 : ℝ) 1) :
    ∀ᵐ y ∂P.trainingCoordinateLaw k,
      normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a∈Icc (0 : ℝ) 1 := by
  filter_upwards [P.training_array_cap_ae (k := k) hcap] with y hy
  exact (totalEmpiricalInstance (reservoirCoordinates.symm y)).normalizedScalarGap_mem_unit
    (totalEmpiricalInstance_bounded _ zero_le_one (fun i j => hy (i,j))) ha

lemma Instance.integrable_empiricalNormalizedGap (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {a : ℝ} (ha : a∈Ioc (0 : ℝ) 1) :
    Integrable (fun y : (Fin n × Fin k) → ℝ =>
      normalizedScalarGap (totalEmpiricalInstance (reservoirCoordinates.symm y)) a) (P.trainingCoordinateLaw k) := by
  apply Integrable.of_bound (measurable_empiricalNormalizedGap ha).aestronglyMeasurable 1
  filter_upwards [P.empiricalNormalizedGap_mem_unit_ae hcap ⟨ha.1.le,ha.2⟩] with y hy
  rw [Real.norm_eq_abs,abs_of_nonneg hy.1]
  exact hy.2

end ProphetSecretary.Model
