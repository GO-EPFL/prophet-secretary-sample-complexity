import ProphetSecretary.Statistics.EmpiricalCapRegret
import ProphetSecretary.Model.SelectedRegretNormalization

/-!
# Normalized regret of the empirical cap policy

Scaling the two coefficients by 1/(1+z) gives the normalized reward-duration
objective. Since the unnormalized regret is nonnegative, normalization can
only reduce its expected value. The selected scalar is still data-dependent.
Paper correspondence: `eq:bayes-empirical-loss`.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model

theorem Learner.empiricalCapAcceptance_normalized_expected_regret_le {n k : ℕ} [NeZero k]
    (Seed : Type) [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (Z : Reservoir n k × Seed → ℝ) (hZ : Measurable Z) {lo : ℝ}
    (hlo : 0<lo) (hlohi : lo≤1/4) (hRange : ∀ p, Z p∈Icc lo (1/4 : ℝ))
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80) :
    (∫ p, optimalScalarValue P (1/(1+Z p)) (Z p/(1+Z p))-
      ((Learner.empiricalCapAcceptance Seed ν Z hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective
        P (1/(1+Z p)) (Z p/(1+Z p)) ∂(P.reservoirLaw k).prod ν) ≤
      empiricalCapRegretConstant lo*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(k : ℝ) := by
  have h := (Learner.empiricalCapAcceptance Seed ν Z hZ).expected_normalized_regret_le_unnormalized
    P (P.integrable_maximum_of_bounded hcap) Z hZ (fun p => hlo.le.trans (hRange p).1)
    (Eventually.of_forall (fun p => (hRange p).2))
  exact h.trans (Learner.empiricalCapAcceptance_expected_regret_le Seed ν Z hZ hlo hlohi hRange P hcap hM)

end ProphetSecretary.Model
