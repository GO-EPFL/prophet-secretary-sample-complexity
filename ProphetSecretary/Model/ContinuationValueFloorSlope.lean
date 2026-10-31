import ProphetSecretary.Model.ContinuationSlope
import ProphetSecretary.Analysis.ThresholdBand

/-!
# An integrated continuation slope above a positive value floor

On a fixed remaining state, the derivative ratio in `upstat:slope` is
integrated over the actual remaining horizon. Continuity at horizon zero is
used, without asserting that the zero-horizon reward value is zero.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma remainingScalarValue_mono_horizon (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z l r : ℝ}
    (hz : 0 ≤ z) (hl : 0 ≤ l) (hlr : l ≤ r) :
    remainingScalarValue P 1 z l ≤ remainingScalarValue P 1 z r :=
  optimalScalarValue_mono P hP zero_le_one (mul_nonneg hz hl) le_rfl
    (mul_le_mul_of_nonneg_left hlr hz)

/-- Explicit reciprocal constant 2(2+hi)/lo for a state whose mean and
remaining horizon are each bounded by B. -/
theorem Instance.remainingScalarValue_increment_ge_floor (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi z B x l r : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hzhi : z ≤ hi) (hB : 0 < B) (hx : 0 < x)
    (hmean : P.totalFirstMoment ≤ B) (hl : 0 ≤ l) (hlr : l ≤ r) (hrB : r ≤ B)
    (hfloor : x / 2 ≤ remainingScalarValue P 1 z l) :
    x * (r - l) ≤ (2 * (2 + hi) / lo) * B *
      (remainingScalarValue P 1 z r - remainingScalarValue P 1 z l) := by
  have hz : 0 < z := hlo.trans_le hloz
  have hhi : 0 < hi := hz.trans_le hzhi
  have hS := P.totalFirstMoment_nonnegative
  let D := 2 * (2 + hi) * B / lo
  have hD : 0 < D := by dsimp [D]; positivity
  let rate := x / D
  have hcont : ContinuousOn (remainingScalarValue P 1 z) (Icc l r) :=
    (remainingScalarValue_continuousOn P hP zero_le_one hz.le).mono (fun t ht => hl.trans ht.1)
  have hdiff : DifferentiableOn ℝ (remainingScalarValue P 1 z) (Ioo l r) :=
    fun t ht => (remainingScalarValue_differentiableAt_all P hP zero_lt_one hz.le (hl.trans_lt ht.1)).differentiableWithinAt
  have hderiv : ∀ t ∈ Ioo l r, rate ≤ deriv (remainingScalarValue P 1 z) t := by
    intro t ht
    have ht0 : 0 < t := hl.trans_lt ht.1
    have htB : t ≤ B := ht.2.le.trans hrB
    have hV := hfloor.trans (remainingScalarValue_mono_horizon P hP hz.le hl ht.1.le)
    have hV0 : 0 ≤ remainingScalarValue P 1 z t := (by positivity : (0 : ℝ) ≤ x / 2).trans hV
    have hden : 0 < 2 * P.totalFirstMoment + z * t := by positivity
    have hzmul : z * t ≤ hi * B := mul_le_mul hzhi htB ht0.le hhi.le
    have hdenle : 2 * P.totalFirstMoment + z * t ≤ (2 + hi) * B := by nlinarith only [hmean, hzmul]
    have hnum : lo * (x / 2) ≤ z * remainingScalarValue P 1 z t :=
      mul_le_mul hloz hV (by positivity) hz.le
    have hratio := div_le_div₀ (mul_nonneg hz.le hV0) hnum hden hdenle
    have heq : lo * (x / 2) / ((2 + hi) * B) = rate := by
      dsimp [rate, D]
      field_simp
    rw [heq] at hratio
    have hactual := remainingScalarValue_deriv_ge_firstMoment_ratio P hP zero_lt_one hz ht0
    simp only [mul_one] at hactual
    exact hratio.trans hactual
  have hslope := ProphetSecretary.Analysis.slopeLowerBoundOn_of_deriv hcont hdiff hderiv
  have hinc := hslope l ⟨le_rfl, hlr⟩ r ⟨hlr, le_rfl⟩ hlr
  have hm := mul_le_mul_of_nonneg_left hinc hD.le
  have heq : D * (rate * (r - l)) = x * (r - l) := by
    dsimp [rate]
    field_simp
  rw [heq] at hm
  have hD_eq : D = (2 * (2 + hi) / lo) * B := by dsimp [D]; ring
  rw [hD_eq] at hm
  exact hm

end ProphetSecretary.Model
