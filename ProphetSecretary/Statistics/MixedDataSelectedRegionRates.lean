import ProphetSecretary.Statistics.MixedDataSelectedRegionBounds
import ProphetSecretary.Statistics.MixedEarlyExpectation
import ProphetSecretary.Statistics.MixedNearExpectation
import ProphetSecretary.Statistics.MixedFarExpectation

/-!
# Actual mixed regional expected rates

The paired actual losses instantiate the constructed mixed entrance moments
and true time-region estimates. The early-band expectations have an explicit
summable majorant. Every constant is the original fixed scalar-interval constant,
independent of known labels and the number of offers.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.mixedDataSelectedClockLoss_near_expectation (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hZ : Measurable Z) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hZrange : ∀ y, Z y ∈ Icc lo hi) (hxk : 1/(k : ℝ) ≤ x) (reverse : Bool) :
    let F := clockRegionLoss P Z hi (4*(hi/lo)*x) (x/2) true
      (fun qt => mixedDataSelectedClockLossDirection P known Z reverse x qt.1 qt.2)
    Integrable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∫ q, F q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalNearRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hz0 : ∀ y, 0 ≤ Z y := fun y => (hlo.trans_le (hZrange y).1).le
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  exact P.mixed_near_expectation_le known hbound hlo hlohi hxk
    (measurable_clockRegionLoss P hP hZ hz0 _ _ _ _
      (measurable_mixedDataSelectedClockLossDirection_pair P known hP hZ hz0 reverse x)).aestronglyMeasurable
    (Filter.Eventually.of_forall (clockRegionLoss_nonnegative P Z _ _ _ _
      (mixedDataSelectedClockLossDirection_nonnegative P known Z reverse x)))
    (P.mixedDataSelectedClockLoss_near_time_bound known hbound hlo hZrange hlohi hx reverse)

theorem Instance.mixedDataSelectedClockLoss_far_expectation (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hZ : Measurable Z) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hZrange : ∀ y, Z y ∈ Icc lo hi) (hxk : 1/(k : ℝ) ≤ x) (reverse : Bool) :
    let F := clockRegionLoss P Z hi (4*(hi/lo)*x) (x/2) false
      (fun qt => mixedDataSelectedClockLossDirection P known Z reverse x qt.1 qt.2)
    Integrable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∫ q, F q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalFarRegretConstant lo hi * x/(k : ℝ) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hz0 : ∀ y, 0 ≤ Z y := fun y => (hlo.trans_le (hZrange y).1).le
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  exact P.mixed_far_expectation_le known hbound hlo hlohi hxk
    (measurable_clockRegionLoss P hP hZ hz0 _ _ _ _
      (measurable_mixedDataSelectedClockLossDirection_pair P known hP hZ hz0 reverse x)).aestronglyMeasurable
    (Filter.Eventually.of_forall (clockRegionLoss_nonnegative P Z _ _ _ _
      (mixedDataSelectedClockLossDirection_nonnegative P known Z reverse x)))
    (P.mixedDataSelectedClockLoss_far_time_bound known hbound hlo hZrange hlohi hx reverse)

theorem Instance.mixedDataSelectedClockLoss_early_expectation_sum (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {Z : ((Fin n × Fin k) → ℝ) → ℝ} {lo hi x : ℝ}
    (hZ : Measurable Z) (hlo : 0 < lo) (hlohi : lo ≤ hi)
    (hZrange : ∀ y, Z y ∈ Icc lo hi) (hxk : 1/(k : ℝ) ≤ x) (reverse : Bool) :
    let F := fun j : ℕ => clockRegionLoss P (fun _ => hi) hi
      (2*((2 : ℝ)^j*(4*(hi/lo)*x))) ((2 : ℝ)^j*(4*(hi/lo)*x)) true
      (fun qt => mixedDataSelectedClockLossDirection P known Z reverse x qt.1 qt.2)
    (∀ j, Integrable (F j) ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))) ∧
      Summable (fun j => ∫ q, F j q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∑' j, ∫ q, F j q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalEarlyRegretConstant lo hi * (1+P.totalFirstMoment)*x/(k : ℝ) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hz0 : ∀ y, 0 ≤ Z y := fun y => (hlo.trans_le (hZrange y).1).le
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have hR : 1 ≤ hi/lo := (le_div_iff₀ hlo).mpr (by simpa using hlohi)
  have hA : 0 < 4*(hi/lo) := by positivity
  apply P.mixed_early_bands_expectation_sum_le known hbound hlo hlohi hxk
    (show x ≤ 4*(hi/lo)*x by nlinarith only [hR,hx])
  · intro j
    exact (measurable_clockRegionLoss P hP measurable_const (fun _ => hhi.le) _ _ _ _
      (measurable_mixedDataSelectedClockLossDirection_pair P known hP hZ hz0 reverse x)).aestronglyMeasurable
  · intro j
    exact Filter.Eventually.of_forall (clockRegionLoss_nonnegative P (fun _ => hi) _ _ _ _
      (mixedDataSelectedClockLossDirection_nonnegative P known Z reverse x))
  · intro j
    have hp : 1 ≤ (2 : ℝ)^j := one_le_pow₀ (by norm_num)
    have hax : 0 < (2 : ℝ)^j*(4*(hi/lo)*x) := by positivity
    have hxj : x ≤ ((2 : ℝ)^j*(4*(hi/lo)*x))/(4*(hi/lo)) := by
      apply (le_div_iff₀ hA).mpr
      nlinarith only [mul_le_mul_of_nonneg_right hp (mul_nonneg hA.le hx.le)]
    exact P.mixedDataSelectedClockLoss_early_time_bound known hbound hlo hZrange hlohi hax hxj reverse

end ProphetSecretary.Model
