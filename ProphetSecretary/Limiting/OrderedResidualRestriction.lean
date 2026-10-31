import ProphetSecretary.Limiting.OrderedBandConvergence

/-!
# Nested upper bands of actual residual measures

Restricting a residual measure already above d to a larger level b gives
exactly its original b-band residual. The same identity holds for the
constructed countable cloud intensity.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting

lemma weightOrderedBandResidual_restrict {n : ℕ} (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ)
    {d b : ℝ} (hdb : d≤b) :
    (weightOrderedBandResidual P w N d).restrict (Ioi b)=weightOrderedBandResidual P w N b := by
  unfold weightOrderedBandResidual
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.restrict_measure_eq,FiniteMeasure.toMeasure_sum,FiniteMeasure.toMeasure_sum]
  ext S hS
  rw [Measure.restrict_apply hS]
  simp only [Measure.coe_finsetSum,Finset.sum_apply,FiniteMeasure.restrict_measure_eq]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.restrict_apply (hS.inter measurableSet_Ioi),Measure.restrict_apply hS]
  congr 1
  rw [inter_assoc,Ioi_inter_Ioi,max_eq_left hdb]

lemma CountableInstance.intensityAbove_restrict (B : CountableInstance) {d b : ℝ}
    (hd : (B.terminal:ℝ)<d) (hb : (B.terminal:ℝ)<b) (hdb : d≤b) :
    (B.intensityAbove d hd).restrict (Ioi b)=B.intensityAbove b hb := by
  apply FiniteMeasure.toMeasure_injective
  change (B.intensity.restrict (Ioi d)).restrict (Ioi b)=B.intensity.restrict (Ioi b)
  exact Measure.restrict_restrict_of_subset (Ioi_subset_Ioi hdb)
end ProphetSecretary.Limiting
