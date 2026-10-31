import ProphetSecretary.Model.ContinuationSlope
import ProphetSecretary.Analysis.ThresholdBand

/-!
# Continuation growth controlled by positive tail count

The derivative bound integrates to every nonnegative remaining horizon,
including horizon zero by continuity. No zero value is imposed at horizon zero.
This supplies the quantitative time growth used in `upmom:transport`.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

theorem remainingScalarValue_positiveCount_growth {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u v : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hu : 0 ≤ u) (huv : u ≤ v) :
    (c / (4 * (1 + P.positiveCount))) * (v - u) ≤
      remainingScalarValue P w c v - remainingScalarValue P w c u := by
  have hcont : ContinuousOn (remainingScalarValue P w c) (Icc (0 : ℝ) v) :=
    (remainingScalarValue_continuousOn P hP hw.le hc.le).mono (fun _ ht => ht.1)
  have hdiff : DifferentiableOn ℝ (remainingScalarValue P w c) (Ioo (0 : ℝ) v) :=
    fun t ht => (remainingScalarValue_hasDerivAt P hP hw hc.le ht.1).differentiableAt.differentiableWithinAt
  have hs := ProphetSecretary.Analysis.slopeLowerBoundOn_of_deriv hcont hdiff
    (fun t ht => remainingScalarValue_deriv_ge_positiveCount_bound P hP hw hc ht.1)
  exact hs u ⟨hu, huv⟩ v ⟨hu.trans huv, le_rfl⟩ huv

end ProphetSecretary.Model
