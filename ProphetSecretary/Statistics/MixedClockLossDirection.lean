import ProphetSecretary.Statistics.MixedClockLossBounds
import ProphetSecretary.Statistics.MixedDataSelectedLossRegions

/-!
# A common direction parameter for the two mixed clock losses

False denotes empirical-rule true loss; true denotes true-rule mixed-design
loss. Joint parameter measurability is independent of the statistical requirement
that the scalar remain fixed during time integration.
-/

open MeasureTheory
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def mixedClockGapLossDirection (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) (z : ℝ) (reverse : Bool) (u : Fin n → ℝ) (x t : ℝ) : ℝ :=
  if reverse then trueClockGapLossMixedEval P known y z u x t else mixedClockGapLoss P known y z u x t

lemma mixedClockGapLossDirection_nonnegative (P : Instance n) (known : Finset (Fin n))
    (y : Reservoir n k) (z : ℝ) (reverse : Bool) (u : Fin n → ℝ) (x t : ℝ) :
    0≤mixedClockGapLossDirection P known y z reverse u x t := by
  cases reverse
  · exact mixedClockGapLoss_nonnegative _ _ _ _ _ _ _
  · exact trueClockGapLossMixedEval_nonnegative _ _ _ _ _ _ _

lemma measurable_mixedClockGapLossDirection {Ω : Type*} [MeasurableSpace Ω]
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {z t x : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hz : Measurable z) (ht : Measurable t) (hx : Measurable x)
    (hu : ∀ j, Measurable (fun ω => u ω j)) (hz0 : ∀ ω, 0≤z ω) (reverse : Bool) :
    Measurable (fun ω => mixedClockGapLossDirection P known (y ω) (z ω) reverse (u ω) (x ω) (t ω)) := by
  cases reverse
  · exact measurable_mixedClockGapLoss P hP known hy hz ht hx hu hz0
  · exact measurable_trueClockGapLossMixedEval P hP known hy hz ht hx hu hz0

lemma mixedClockGapLossDirection_bounded (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (y : Reservoir n k) (hy : ∀ j l, y j l≤1)
    {z hi t : ℝ} (hz : 0≤z) (hzhi : z≤hi) (ht : 0≤t) (reverse : Bool) (u : Fin n → ℝ) (x : ℝ) :
    mixedClockGapLossDirection P known y z reverse u x t≤2+2*hi := by
  cases reverse
  · exact (paired_mixedClockGapLoss_bounded P known hbound y hy hz hzhi ht u x).1
  · exact (paired_mixedClockGapLoss_bounded P known hbound y hy hz hzhi ht u x).2

lemma mixedDataSelectedClockLossDirection_eq (P : Instance n) (known : Finset (Fin n))
    (Z : ((Fin n × Fin k) → ℝ) → ℝ) (reverse : Bool) (x : ℝ)
    (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) (t : ℝ) :
    mixedDataSelectedClockLossDirection P known Z reverse x q t =
      mixedClockGapLossDirection P known (reservoirCoordinates.symm q.1) (Z q.1) reverse q.2 x t := rfl

end ProphetSecretary.Model
