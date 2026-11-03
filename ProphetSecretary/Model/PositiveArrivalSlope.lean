import ProphetSecretary.Model.PositiveArrivalDuration
import ProphetSecretary.Model.PositiveCountGrowth

/-!
# Sharp remaining-horizon growth from the positive arrival count

The zero-rejecting canonical policy waits at least as long as the first
positive arrival. Its reciprocal-count duration floor gives the slope used
in `eq:calibration-time-slope`. The variable is remaining horizon.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

/-- The canonical envelope derivative has the sharp positive-count floor. -/
lemma remainingScalarValue_deriv_ge_reciprocal_positiveCount {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hu : 0 < u) :
    c / (1 + P.positiveCount) ≤ deriv (remainingScalarValue P w c) u := by
  rw [remainingScalarValue_deriv_eq_canonicalDuration P hP hw hc.le hu]
  have hT := P.valuePolicy_duration_ge_reciprocal_positiveCount hP hw (mul_pos hc hu) P
  have h := mul_le_mul_of_nonneg_left hT hc.le
  simpa only [mul_one_div] using h

/-- `eq:calibration-time-slope`, including horizon zero by continuity. -/
theorem remainingScalarValue_reciprocal_positiveCount_growth {n : ℕ} (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c u v : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hu : 0 ≤ u) (huv : u ≤ v) :
    (c / (1 + P.positiveCount)) * (v - u) ≤
      remainingScalarValue P w c v - remainingScalarValue P w c u := by
  have hcont : ContinuousOn (remainingScalarValue P w c) (Icc (0 : ℝ) v) :=
    (remainingScalarValue_continuousOn P hP hw.le hc.le).mono (fun _ ht => ht.1)
  have hdiff : DifferentiableOn ℝ (remainingScalarValue P w c) (Ioo (0 : ℝ) v) :=
    fun t ht => (remainingScalarValue_hasDerivAt P hP hw hc.le ht.1).differentiableAt.differentiableWithinAt
  have hs := ProphetSecretary.Analysis.slopeLowerBoundOn_of_deriv hcont hdiff
    (fun t ht => remainingScalarValue_deriv_ge_reciprocal_positiveCount P hP hw hc ht.1)
  exact hs u ⟨hu, huv⟩ v ⟨hu.trans huv, le_rfl⟩ huv

end ProphetSecretary.Model
