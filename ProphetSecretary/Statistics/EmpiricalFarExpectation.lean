import ProphetSecretary.Statistics.EmpiricalNearExpectation
import ProphetSecretary.Analysis.EmpiricalExpectedFar

/-!
# Expected far-region loss with the actual entrance envelope

The sixth moment is supplied by the constructed entrance error, not assumed.
The input time-window domination is the one proved in `ClockFarLoss`; the
post-entrance point itself has zero Lebesgue measure.
-/

open MeasureTheory Filter

namespace ProphetSecretary.Model

noncomputable def empiricalFarRegretConstant (lo hi : ℝ) : ℝ :=
  64 * (1 / (2 * lo)) * empiricalSixthMomentConstant lo hi * max ((4 * (hi / lo)) ^ 3) 1

variable {n k : ℕ} [NeZero k]

theorem Instance.empirical_far_expectation_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi x : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hxk : 1 / (k : ℝ) ≤ x)
    {F : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm : AEStronglyMeasurable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)))
    (hF0 : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ F q)
    (hdom : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      F q ≤ ((1 / (2 * lo)) * x) *
        (if x / 2 ≤ P.entranceFutureError k lo hi (4 * (hi / lo) * x) q then
          P.entranceFutureError k lo hi (4 * (hi / lo) * x) q else 0)) :
    Integrable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∫ q, F q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalFarRegretConstant lo hi * x / (k : ℝ) := by
  let A := 4 * (hi / lo)
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw := P.entranceFutureError_moment (k := k) (p := 6) hbound
    hlo.le hlohi hhi (mul_nonneg hA hx.le) (Or.inr rfl)
  rw [empiricalRestartMomentBound_six, mul_pow] at hw
  have h := ProphetSecretary.Analysis.empirical_expected_far_le μ hm hF0
    (P.measurable_entranceFutureError lo hi (A * x))
    (Filter.Eventually.of_forall (P.entranceFutureError_nonnegative lo hi (A * x))) hw.1 hk hxk
    (by positivity : 0 ≤ 1 / (2 * lo)) (empiricalSixthMomentConstant_nonnegative hhi) hdom hw.2
  simpa only [empiricalFarRegretConstant, A] using h

end ProphetSecretary.Model
