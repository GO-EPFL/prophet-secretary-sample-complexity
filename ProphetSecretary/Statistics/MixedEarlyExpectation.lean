import ProphetSecretary.Statistics.MixedEntranceFutureMoments
import ProphetSecretary.Statistics.EmpiricalEarlyExpectation

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

theorem Instance.mixed_early_band_expectation_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (ha : 0 < a)
    {F : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm : AEStronglyMeasurable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)))
    (hF0 : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ F q)
    (hdom : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      F q ≤ (empiricalEarlyTimeConstant lo hi / a ^ 5) *
        (P.entranceRemainingSize hi (2 * a) q.2 * P.mixedEntranceFutureError known k lo hi (2 * a) q ^ 6)) :
    Integrable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∫ q, F q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalEarlyRegretCoefficient lo hi * (1 + P.totalFirstMoment) *
          (1 / (a * (k : ℝ) ^ 3) + 1 / (a ^ 4 * (k : ℝ) ^ 6)) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hw := P.mixedEntranceFutureError_weighted_moment (k := k) (p := 6) known hbound
    hlo.le hlohi hhi (by positivity : 0 ≤ 2 * a) (Or.inr rfl)
  rw [empiricalRestartMomentBound_six] at hw
  have h := ProphetSecretary.Analysis.empirical_expected_early_le μ hm hF0 hw.1 hk ha
    (empiricalEarlyTimeConstant_nonnegative hlo hhi) (empiricalSixthMomentConstant_nonnegative hhi)
    P.totalFirstMoment_nonnegative hhi hdom hw.2
  simpa only [empiricalEarlyRegretCoefficient] using h

theorem Instance.mixed_early_bands_expectation_sum_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a x : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hxk : 1 / (k : ℝ) ≤ x) (hxa : x ≤ a)
    {F : ℕ → (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm : ∀ j, AEStronglyMeasurable (F j) ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)))
    (hF0 : ∀ j, ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ F j q)
    (hdom : ∀ j, ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      F j q ≤ (empiricalEarlyTimeConstant lo hi / ((2 : ℝ) ^ j * a) ^ 5) *
        (P.entranceRemainingSize hi (2 * ((2 : ℝ) ^ j * a)) q.2 *
          P.mixedEntranceFutureError known k lo hi (2 * ((2 : ℝ) ^ j * a)) q ^ 6)) :
    (∀ j, Integrable (F j) ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))) ∧
      Summable (fun j => ∫ q, F j q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∑' j, ∫ q, F j q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalEarlyRegretConstant lo hi * (1 + P.totalFirstMoment) * x / (k : ℝ) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hhi := hlo.trans_le hlohi
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have ha := hx.trans_le hxa
  have hband (j : ℕ) := P.mixed_early_band_expectation_le known hbound hlo hlohi
    (by positivity : 0 < (2 : ℝ) ^ j * a) (hm j) (hF0 j) (hdom j)
  have hS := P.totalFirstMoment_nonnegative
  have hD : 0 ≤ empiricalEarlyRegretCoefficient lo hi * (1 + P.totalFirstMoment) :=
    mul_nonneg (empiricalEarlyRegretCoefficient_nonnegative hlo hhi) (by linarith only [hS])
  have h := ProphetSecretary.Analysis.empirical_early_rates_summable hk hxk hxa hD
    (fun j => integral_nonneg_of_ae (hF0 j)) (fun j => (hband j).2)
  refine ⟨fun j => (hband j).1, h.1, ?_⟩
  have heq : 4 * (empiricalEarlyRegretCoefficient lo hi * (1 + P.totalFirstMoment)) * x / (k : ℝ) =
      empiricalEarlyRegretConstant lo hi * (1 + P.totalFirstMoment) * x / (k : ℝ) := by
    unfold empiricalEarlyRegretConstant
    ring
  exact h.2.trans_eq heq

end ProphetSecretary.Model
