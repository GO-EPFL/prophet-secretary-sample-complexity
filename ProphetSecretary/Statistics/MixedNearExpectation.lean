import ProphetSecretary.Statistics.MixedEntranceFutureMoments
import ProphetSecretary.Statistics.EmpiricalNearExpectation

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

theorem Instance.mixed_near_expectation_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi x : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hxk : 1 / (k : ℝ) ≤ x)
    {F : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm : AEStronglyMeasurable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)))
    (hF0 : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ F q)
    (hdom : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      F q ≤ ((4 * (2 + hi) / lo) / x) *
        (P.entranceRemainingSize hi (4 * (hi / lo) * x) q.2 *
          P.mixedEntranceFutureError known k lo hi (4 * (hi / lo) * x) q ^ 2)) :
    Integrable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∫ q, F q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalNearRegretConstant lo hi * (1 + P.totalFirstMoment) * x / (k : ℝ) := by
  let A := 4 * (hi / lo)
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hC : 0 ≤ 4 * (2 + hi) / lo := by positivity
  have hw := P.mixedEntranceFutureError_weighted_moment (k := k) (p := 2) known hbound
    hlo.le hlohi hhi (mul_nonneg hA hx.le) (Or.inl rfl)
  rw [empiricalRestartMomentBound_two] at hw
  have h := ProphetSecretary.Analysis.empirical_expected_near_le μ hm hF0 hw.1 hk hxk hA hC
    (empiricalSecondMomentConstant_nonnegative hhi) P.totalFirstMoment_nonnegative hhi hdom hw.2
  simpa only [empiricalNearRegretConstant, A] using h

end ProphetSecretary.Model
