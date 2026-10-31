import ProphetSecretary.Statistics.MixedEntranceFutureMoments
import ProphetSecretary.Statistics.EmpiricalFarExpectation

/-!
# Actual expected mixed regional loss

The constructed mixed entrance moments supply every statistical moment input.
The remaining elementary measurable time-loss domination is explicit. Constants
are the original scalar-interval constants and are uniform in known identities.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.mixed_far_expectation_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi x : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hxk : 1 / (k : ℝ) ≤ x)
    {F : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm : AEStronglyMeasurable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)))
    (hF0 : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ F q)
    (hdom : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      F q ≤ ((1 / (2 * lo)) * x) *
        (if x / 2 ≤ P.mixedEntranceFutureError known k lo hi (4 * (hi / lo) * x) q then
          P.mixedEntranceFutureError known k lo hi (4 * (hi / lo) * x) q else 0)) :
    Integrable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∫ q, F q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalFarRegretConstant lo hi * x / (k : ℝ) := by
  let A := 4 * (hi / lo)
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hw := P.mixedEntranceFutureError_moment (k := k) (p := 6) known hbound
    hlo.le hlohi hhi (mul_nonneg hA hx.le) (Or.inr rfl)
  rw [empiricalRestartMomentBound_six, mul_pow] at hw
  have h := ProphetSecretary.Analysis.empirical_expected_far_le μ hm hF0
    (P.measurable_mixedEntranceFutureError known lo hi (A * x))
    (Filter.Eventually.of_forall (P.mixedEntranceFutureError_nonnegative known lo hi (A * x))) hw.1 hk hxk
    (by positivity : 0 ≤ 1 / (2 * lo)) (empiricalSixthMomentConstant_nonnegative hhi) hdom hw.2
  simpa only [empiricalFarRegretConstant, A] using h

end ProphetSecretary.Model
