import ProphetSecretary.Statistics.EmpiricalFarExpectation
import ProphetSecretary.Analysis.EmpiricalExpectedEarly

/-!
# Actual entrance moments in the early-band expectation bound

Every band uses its own constructed entrance at level 2a. Joint post-size
sixth moments supply the inverse-power profile, and the dyadic sum has a
constant independent of the number of offers or bands.
-/

open MeasureTheory Filter
open scoped BigOperators

namespace ProphetSecretary.Model

noncomputable def empiricalEarlyTimeConstant (lo hi : ℝ) : ℝ :=
  (32 * (2 + hi) / lo) * (hi / lo) ^ 5
noncomputable def empiricalEarlyRegretCoefficient (lo hi : ℝ) : ℝ :=
  16 * empiricalEarlyTimeConstant lo hi * empiricalSixthMomentConstant lo hi / hi
noncomputable def empiricalEarlyRegretConstant (lo hi : ℝ) : ℝ :=
  4 * empiricalEarlyRegretCoefficient lo hi

lemma empiricalEarlyTimeConstant_nonnegative {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi) :
    0 ≤ empiricalEarlyTimeConstant lo hi := by unfold empiricalEarlyTimeConstant; positivity

lemma empiricalEarlyRegretCoefficient_nonnegative {lo hi : ℝ} (hlo : 0 < lo) (hhi : 0 < hi) :
    0 ≤ empiricalEarlyRegretCoefficient lo hi := by
  have hC := empiricalEarlyTimeConstant_nonnegative hlo hhi
  have hC₆ := empiricalSixthMomentConstant_nonnegative (lo := lo) hhi
  unfold empiricalEarlyRegretCoefficient
  positivity

variable {n k : ℕ} [NeZero k]

theorem Instance.empirical_early_band_expectation_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (ha : 0 < a)
    {F : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm : AEStronglyMeasurable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)))
    (hF0 : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ F q)
    (hdom : ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      F q ≤ (empiricalEarlyTimeConstant lo hi / a ^ 5) *
        (P.entranceRemainingSize hi (2 * a) q.2 * P.entranceFutureError k lo hi (2 * a) q ^ 6)) :
    Integrable F ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∫ q, F q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalEarlyRegretCoefficient lo hi * (1 + P.totalFirstMoment) *
          (1 / (a * (k : ℝ) ^ 3) + 1 / (a ^ 4 * (k : ℝ) ^ 6)) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hhi : 0 < hi := hlo.trans_le hlohi
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hw := P.entranceFutureError_weighted_moment (k := k) (p := 6) hbound
    hlo.le hlohi hhi (by positivity : 0 ≤ 2 * a) (Or.inr rfl)
  rw [empiricalRestartMomentBound_six] at hw
  have h := ProphetSecretary.Analysis.empirical_expected_early_le μ hm hF0 hw.1 hk ha
    (empiricalEarlyTimeConstant_nonnegative hlo hhi) (empiricalSixthMomentConstant_nonnegative hhi)
    P.totalFirstMoment_nonnegative hhi hdom hw.2
  simpa only [empiricalEarlyRegretCoefficient] using h

theorem Instance.empirical_early_bands_expectation_sum_le (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a x : ℝ}
    (hlo : 0 < lo) (hlohi : lo ≤ hi) (hxk : 1 / (k : ℝ) ≤ x) (hxa : x ≤ a)
    {F : ℕ → (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ}
    (hm : ∀ j, AEStronglyMeasurable (F j) ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)))
    (hF0 : ∀ j, ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n), 0 ≤ F j q)
    (hdom : ∀ j, ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      F j q ≤ (empiricalEarlyTimeConstant lo hi / ((2 : ℝ) ^ j * a) ^ 5) *
        (P.entranceRemainingSize hi (2 * ((2 : ℝ) ^ j * a)) q.2 *
          P.entranceFutureError k lo hi (2 * ((2 : ℝ) ^ j * a)) q ^ 6)) :
    (∀ j, Integrable (F j) ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))) ∧
      Summable (fun j => ∫ q, F j q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
      (∑' j, ∫ q, F j q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
        empiricalEarlyRegretConstant lo hi * (1 + P.totalFirstMoment) * x / (k : ℝ) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hhi := hlo.trans_le hlohi
  have hk : 0 < (k : ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero (NeZero.ne k))
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have ha := hx.trans_le hxa
  have hband (j : ℕ) := P.empirical_early_band_expectation_le hbound hlo hlohi
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
