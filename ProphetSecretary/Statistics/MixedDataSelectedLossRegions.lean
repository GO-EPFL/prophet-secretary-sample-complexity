import ProphetSecretary.Statistics.MixedDataSelectedClockLoss
import ProphetSecretary.Statistics.DataSelectedLossRegions

/-!
# Both mixed selected-weight directions on actual time regions

The time regions and their integrals use the TRUE continuation curve. The mixed
actual loss is measurable jointly and in each fixed time section. One scalar
selected from data remains fixed throughout time integration.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ}

noncomputable def mixedDataSelectedClockLossDirection (P : Instance n) (known : Finset (Fin n)) [NeZero k]
    (Z : ((Fin n × Fin k) → ℝ) → ℝ) (reverse : Bool) (x : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) : ℝ :=
  if reverse then mixedDataSelectedClockLossReverse P known Z x q t else mixedDataSelectedClockLoss P known Z x q t

lemma measurable_mixedDataSelectedClockLossDirection_pair (P : Instance n) (known : Finset (Fin n)) [NeZero k]
    (hP : Integrable Instance.maximum P.valuesLaw)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} (hZ : Measurable Z) (hZ0 : ∀ a, 0 ≤ Z a)
    (reverse : Bool) (x : ℝ) :
    Measurable (fun qt : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) =>
      mixedDataSelectedClockLossDirection P known Z reverse x qt.1 qt.2) := by
  cases reverse
  · exact (measurable_mixedDataSelectedClockLoss_pair P known hP hZ hZ0 x).1
  · exact (measurable_mixedDataSelectedClockLoss_pair P known hP hZ hZ0 x).2

lemma mixedDataSelectedClockLossDirection_nonnegative (P : Instance n) (known : Finset (Fin n)) [NeZero k]
    (Z : ((Fin n × Fin k) → ℝ) → ℝ) (reverse : Bool) (x : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) :
    0 ≤ mixedDataSelectedClockLossDirection P known Z reverse x q t := by
  cases reverse
  · exact mixedDataSelectedClockLoss_nonnegative _ _ _ _ _ _
  · exact mixedDataSelectedClockLossReverse_nonnegative _ _ _ _ _ _

lemma measurable_mixedDataSelectedClockLossDirection_time (P : Instance n) (known : Finset (Fin n)) [NeZero k]
    (hP : Integrable Instance.maximum P.valuesLaw)
    (Z : ((Fin n × Fin k) → ℝ) → ℝ) (hZ0 : ∀ a, 0 ≤ Z a)
    (reverse : Bool) (x : ℝ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    Measurable (fun t => mixedDataSelectedClockLossDirection P known Z reverse x q t) := by
  cases reverse
  · exact measurable_mixedClockGapLoss P hP known (fun _ _ => measurable_const)
      measurable_const measurable_id measurable_const (fun _ => measurable_const) (fun _ => hZ0 q.1)
  · exact measurable_trueClockGapLossMixedEval P hP known (fun _ _ => measurable_const)
      measurable_const measurable_id measurable_const (fun _ => measurable_const) (fun _ => hZ0 q.1)

end ProphetSecretary.Model
