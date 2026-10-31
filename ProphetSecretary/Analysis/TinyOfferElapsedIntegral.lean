import ProphetSecretary.Analysis.ThresholdBand

/-!
# Integrating the tiny-offer region in elapsed time

Only elapsed times with remaining horizon 1−t≤x/lo can contribute. A
nonnegative expected loss bounded there by x+(2S+hi)(1−t) has integral at most K(lo,hi)(1+S)x², with an
explicit K. The estimate remains valid when x/lo exceeds the unit horizon.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Analysis

theorem tiny_offer_elapsed_integral_le {loss : ℝ → ℝ} {lo hi S x : ℝ}
    (hlo : 0 < lo) (hhi : 0 ≤ hi) (hS : 0 ≤ S) (hx : 0 ≤ x)
    (hm : AEStronglyMeasurable loss (volume.restrict (Icc (0 : ℝ) 1)))
    (h0 : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), 0 ≤ loss t)
    (hdom : ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1),
      loss t ≤ (Icc (1 - x / lo) 1).indicator (fun t => x + (2 * S + hi) * (1 - t)) t) :
    (∫ t in Icc (0 : ℝ) 1, loss t) ≤
      (1 / lo + (2 + hi) / lo ^ 2) * (1 + S) * x ^ 2 := by
  let μ := volume.restrict (Icc (0 : ℝ) 1)
  let T := Icc (1 - x / lo) (1 : ℝ)
  let M := x + (2 * S + hi) * (x / lo)
  have hw : 0 ≤ x / lo := div_nonneg hx hlo.le
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hbound : ∀ᵐ t ∂μ, loss t ≤ T.indicator (fun _ => M) t := by
    filter_upwards [hdom] with t hu
    apply hu.trans
    by_cases ht : t ∈ T
    · rw [Set.indicator_of_mem ht, Set.indicator_of_mem ht]
      dsimp [M]
      have htime : 1 - t ≤ x / lo := by linarith only [ht.1]
      exact add_le_add le_rfl (mul_le_mul_of_nonneg_left htime (by positivity))
    · rw [Set.indicator_of_notMem ht, Set.indicator_of_notMem ht]
  have hAbs : ∀ᵐ t ∂μ, ‖loss t‖ ≤ M := by
    filter_upwards [h0, hbound] with t hu hb
    rw [Real.norm_eq_abs, abs_of_nonneg hu]
    apply hb.trans
    by_cases ht : t ∈ T <;> simp [ht, hM]
  have hI : Integrable loss μ := Integrable.of_bound hm M hAbs
  have hTI : Integrable (T.indicator (fun _ => M)) μ := (integrable_const M).indicator measurableSet_Icc
  have hint := integral_mono_ae hI hTI hbound
  rw [integral_indicator_const M measurableSet_Icc, smul_eq_mul] at hint
  have hvol : μ.real T ≤ x / lo := by
    have hmT : volume T < ⊤ := by simp [T, Real.volume_Icc]
    have hle : μ T ≤ volume T := Measure.restrict_le_self T
    have hreal := ENNReal.toReal_mono hmT.ne hle
    simpa only [T, Measure.real, Real.volume_Icc, sub_sub_cancel, ENNReal.toReal_ofReal hw] using hreal
  have hprod := mul_le_mul_of_nonneg_right hvol hM
  have hc : 2 * S + hi ≤ (2 + hi) * (1 + S) := by nlinarith only [hS, hhi]
  have hm : M ≤ (1 + S) * (x + (2 + hi) * (x / lo)) := by
    have h1 := mul_le_mul_of_nonneg_right hc hw
    have h2 : x ≤ (1 + S) * x := by nlinarith only [hS, hx]
    dsimp [M]
    nlinarith only [h1, h2]
  have hfinal := mul_le_mul_of_nonneg_left hm hw
  have heq : (x / lo) * ((1 + S) * (x + (2 + hi) * (x / lo))) =
      (1 / lo + (2 + hi) / lo ^ 2) * (1 + S) * x ^ 2 := by ring
  exact (hint.trans hprod).trans (hfinal.trans_eq heq)

end ProphetSecretary.Analysis
