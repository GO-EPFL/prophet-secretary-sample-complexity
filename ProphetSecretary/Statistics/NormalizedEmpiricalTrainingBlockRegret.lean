import ProphetSecretary.Statistics.EmpiricalTrainingBlockRegret
import ProphetSecretary.Model.SelectedRegretNormalization

/-! # Normalized selected-weight regret on an actual independent empirical block -/

open MeasureTheory Set Filter
namespace ProphetSecretary.Model
variable {n m c : ℕ} [NeZero m] {Seed : Type} [MeasurableSpace Seed]

theorem Learner.empiricalTrainingBlock_normalized_expected_regret_le (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z)
    {lo : ℝ} (hlo : 0<lo) (hlohi : lo≤1/4) (hRange : ∀ p, Z p∈Icc lo (1/4 : ℝ))
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80) :
    (∫ p, optimalScalarValue P (1/(1+Z p)) (Z p/(1+Z p))-
      ((Learner.empiricalTrainingBlock ν e Z hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective
        P (1/(1+Z p)) (Z p/(1+Z p)) ∂(P.reservoirLaw c).prod ν) ≤
      empiricalCapRegretConstant lo*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ) := by
  have h := (Learner.empiricalTrainingBlock ν e Z hZ).expected_normalized_regret_le_unnormalized
    P (P.integrable_maximum_of_bounded hcap) Z hZ (fun p => hlo.le.trans (hRange p).1)
    (Eventually.of_forall (fun p => (hRange p).2))
  exact h.trans (Learner.empiricalTrainingBlock_expected_regret_le ν e Z hZ hlo hlohi hRange P hcap hM)

end ProphetSecretary.Model
