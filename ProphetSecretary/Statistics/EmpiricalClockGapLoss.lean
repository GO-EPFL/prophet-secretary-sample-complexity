import ProphetSecretary.Model.StateValueCoefficientMeasurability
import ProphetSecretary.Model.CanonicalLossMeasurability

/-!
# Actual clock-path comparison losses for an excluded candidate

Both loss directions use the true candidate gap for support. They depend on
other-variable training, clocks and a scalar that is fixed during time
integration. Joint measurability supports averaging training-selected scalars
without invoking any centering at that selected scalar.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def empiricalClockGapLoss (P : Instance n) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t : ℝ) : ℝ :=
  ProphetSecretary.Analysis.gapLoss (decide (0≤x-(totalEmpiricalInstance y).clockContinuation z u t))
    (x-P.clockContinuation z u t)

noncomputable def trueClockGapLossEmpiricalEval (P : Instance n) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t : ℝ) : ℝ :=
  ProphetSecretary.Analysis.gapLoss (decide (0≤x-P.clockContinuation z u t))
    (x-(totalEmpiricalInstance y).clockContinuation z u t)

lemma empiricalClockGapLoss_nonnegative (P : Instance n) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t : ℝ) : 0≤empiricalClockGapLoss P y z u x t :=
  ProphetSecretary.Analysis.gapLoss_nonnegative _ _

lemma trueClockGapLossEmpiricalEval_nonnegative (P : Instance n) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t : ℝ) : 0≤trueClockGapLossEmpiricalEval P y z u x t :=
  ProphetSecretary.Analysis.gapLoss_nonnegative _ _

lemma measurable_empiricalClockGapLoss {Ω : Type*} [MeasurableSpace Ω] (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {y : Ω → Reservoir n k} {z t x : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hz : Measurable z) (ht : Measurable t) (hx : Measurable x)
    (hu : ∀ j, Measurable (fun ω => u ω j)) (hz0 : ∀ ω, 0≤z ω) :
    Measurable (fun ω => empiricalClockGapLoss P (y ω) (z ω) (u ω) (x ω) (t ω)) := by
  have htrue := P.measurable_clockContinuation_parameters hP hz ht hu hz0
  have hemp := measurable_totalEmpirical_clockContinuation_parameters hy hz ht hu hz0
  exact ProphetSecretary.Analysis.measurable_threshold_gapLoss (hx.sub htrue) (hx.sub hemp)

lemma measurable_trueClockGapLossEmpiricalEval {Ω : Type*} [MeasurableSpace Ω] (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {y : Ω → Reservoir n k} {z t x : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hz : Measurable z) (ht : Measurable t) (hx : Measurable x)
    (hu : ∀ j, Measurable (fun ω => u ω j)) (hz0 : ∀ ω, 0≤z ω) :
    Measurable (fun ω => trueClockGapLossEmpiricalEval P (y ω) (z ω) (u ω) (x ω) (t ω)) := by
  have htrue := P.measurable_clockContinuation_parameters hP hz ht hu hz0
  have hemp := measurable_totalEmpirical_clockContinuation_parameters hy hz ht hu hz0
  exact ProphetSecretary.Analysis.measurable_threshold_gapLoss (hx.sub hemp) (hx.sub htrue)

/-- Both actual losses use the true gap band, with threshold equality retained. -/
theorem paired_clockGapLoss_bound (P : Instance n) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t E : ℝ)
    (hError : |P.clockContinuation z u t-(totalEmpiricalInstance y).clockContinuation z u t|≤E) :
    empiricalClockGapLoss P y z u x t ≤ (if |x-P.clockContinuation z u t|≤E then E else 0) ∧
      trueClockGapLossEmpiricalEval P y z u x t ≤ (if |x-P.clockContinuation z u t|≤E then E else 0) := by
  have hgap : |(x-P.clockContinuation z u t)-(x-(totalEmpiricalInstance y).clockContinuation z u t)|≤E := by
    have heq : (x-P.clockContinuation z u t)-(x-(totalEmpiricalInstance y).clockContinuation z u t) =
      (totalEmpiricalInstance y).clockContinuation z u t-P.clockContinuation z u t := by ring
    rw [heq,abs_sub_comm]
    exact hError
  exact ProphetSecretary.Analysis.paired_gapLoss_bound hgap

end ProphetSecretary.Model
