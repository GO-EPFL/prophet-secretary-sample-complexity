import ProphetSecretary.Statistics.EntranceFutureMoments
import ProphetSecretary.Statistics.EmpiricalMomentCoefficients
import ProphetSecretary.Analysis.EmpiricalExpectedNear

/-!
# Expected near-region loss with the actual entrance moments

The joint moment is that of the constructed post-entrance size and envelope.
Only the elementary time-loss domination is an input. No entrance moment or
restart-independence assertion is assumed. The final constant depends only on
lo and hi, before choosing the finite instance or candidate value.
-/

open MeasureTheory Filter

namespace ProphetSecretary.Model

noncomputable def empiricalNearRegretConstant (lo hi : ℝ) : ℝ :=
  ((4 * (2 + hi) / lo) * empiricalSecondMomentConstant lo hi * (4 * (hi / lo)) *
    (4 * (hi / lo) + 1) / hi)

variable {n k : ℕ} [NeZero k]

theorem Instance.empirical_near_expectation_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi x : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hxk : 1 / (k : ℝ) ≤ x)
    {F : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm : AEStronglyMeasurable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)))
    (hF0 : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ F q)
    (hdom : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      F q ≤ ((4 * (2 + hi) / lo) / x) *
        (P.entranceRemainingSize hi (4 * (hi / lo) * x) q.2 *
          P.entranceFutureError k lo hi (4 * (hi / lo) * x) q ^ 2)) :
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
  have hw := P.entranceFutureError_weighted_moment (k := k) (p := 2) hbound
    hlo.le hlohi hhi (mul_nonneg hA hx.le) (Or.inl rfl)
  rw [empiricalRestartMomentBound_two] at hw
  have h := ProphetSecretary.Analysis.empirical_expected_near_le μ hm hF0 hw.1 hk hxk hA hC
    (empiricalSecondMomentConstant_nonnegative hhi) P.totalFirstMoment_nonnegative hhi hdom hw.2
  simpa only [empiricalNearRegretConstant, A] using h

end ProphetSecretary.Model
