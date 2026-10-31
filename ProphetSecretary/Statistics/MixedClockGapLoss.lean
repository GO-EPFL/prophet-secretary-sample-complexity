import ProphetSecretary.Model.MixedStateValueMeasurability
import ProphetSecretary.Model.CanonicalLossMeasurability

/-!
# Actual paired clock losses for mixed design laws

Both directions use the TRUE candidate-gap support and one scalar fixed during
time integration. They retain all other samples and clocks. Exact known laws
replace empirical laws only at their declared identities; joint measurability
does not introduce centering after a scalar is selected from the data.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

noncomputable def mixedClockGapLoss (P : Instance n) (known : Finset (Fin n)) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t : ℝ) : ℝ :=
  ProphetSecretary.Analysis.gapLoss (decide (0≤x-(mixedEmpiricalInstance P known y).clockContinuation z u t))
    (x-P.clockContinuation z u t)

noncomputable def trueClockGapLossMixedEval (P : Instance n) (known : Finset (Fin n)) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t : ℝ) : ℝ :=
  ProphetSecretary.Analysis.gapLoss (decide (0≤x-P.clockContinuation z u t))
    (x-(mixedEmpiricalInstance P known y).clockContinuation z u t)

lemma mixedClockGapLoss_nonnegative (P : Instance n) (known : Finset (Fin n)) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t : ℝ) : 0≤mixedClockGapLoss P known y z u x t :=
  ProphetSecretary.Analysis.gapLoss_nonnegative _ _

lemma trueClockGapLossMixedEval_nonnegative (P : Instance n) (known : Finset (Fin n)) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t : ℝ) : 0≤trueClockGapLossMixedEval P known y z u x t :=
  ProphetSecretary.Analysis.gapLoss_nonnegative _ _

lemma measurable_mixedClockGapLoss {Ω : Type*} [MeasurableSpace Ω] (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {z t x : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hz : Measurable z) (ht : Measurable t) (hx : Measurable x)
    (hu : ∀ j, Measurable (fun ω => u ω j)) (hz0 : ∀ ω, 0≤z ω) :
    Measurable (fun ω => mixedClockGapLoss P known (y ω) (z ω) (u ω) (x ω) (t ω)) := by
  have htrue := P.measurable_clockContinuation_parameters hP hz ht hu hz0
  have hemp := measurable_mixed_clockContinuation_parameters P hP known hy hz ht hu hz0
  exact ProphetSecretary.Analysis.measurable_threshold_gapLoss (hx.sub htrue) (hx.sub hemp)

lemma measurable_trueClockGapLossMixedEval {Ω : Type*} [MeasurableSpace Ω] (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {z t x : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ j l, Measurable (fun ω => y ω j l)) (hz : Measurable z) (ht : Measurable t) (hx : Measurable x)
    (hu : ∀ j, Measurable (fun ω => u ω j)) (hz0 : ∀ ω, 0≤z ω) :
    Measurable (fun ω => trueClockGapLossMixedEval P known (y ω) (z ω) (u ω) (x ω) (t ω)) := by
  have htrue := P.measurable_clockContinuation_parameters hP hz ht hu hz0
  have hemp := measurable_mixed_clockContinuation_parameters P hP known hy hz ht hu hz0
  exact ProphetSecretary.Analysis.measurable_threshold_gapLoss (hx.sub hemp) (hx.sub htrue)

/-- Both actual losses use the true gap band, with threshold equality retained. -/
theorem paired_mixedClockGapLoss_bound (P : Instance n) (known : Finset (Fin n)) (y : Reservoir n k)
    (z : ℝ) (u : Fin n → ℝ) (x t E : ℝ)
    (hError : |P.clockContinuation z u t-(mixedEmpiricalInstance P known y).clockContinuation z u t|≤E) :
    mixedClockGapLoss P known y z u x t ≤ (if |x-P.clockContinuation z u t|≤E then E else 0) ∧
      trueClockGapLossMixedEval P known y z u x t ≤ (if |x-P.clockContinuation z u t|≤E then E else 0) := by
  have hgap : |(x-P.clockContinuation z u t)-(x-(mixedEmpiricalInstance P known y).clockContinuation z u t)|≤E := by
    have heq : (x-P.clockContinuation z u t)-(x-(mixedEmpiricalInstance P known y).clockContinuation z u t) =
      (mixedEmpiricalInstance P known y).clockContinuation z u t-P.clockContinuation z u t := by ring
    rw [heq,abs_sub_comm]
    exact hError
  exact ProphetSecretary.Analysis.paired_gapLoss_bound hgap

end ProphetSecretary.Model
