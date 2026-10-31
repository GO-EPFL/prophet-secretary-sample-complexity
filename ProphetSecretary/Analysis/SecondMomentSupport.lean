import ProphetSecretary.Analysis.SumIntegralCauchy
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-!
# A one-sixth support bound from two moments

For nonnegative N with mean r≥2 and second moment at most r²+r, the positive
part of N−1 has mean at least r/2 and second moment at most 3r²/2.
Cauchy--Schwarz gives probability at least 1/6 of N>1. Applied to an integer
count this is the at-least-two estimate in the aggregate-atom argument.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Analysis

variable {Ω : Type*} [MeasurableSpace Ω]

theorem probability_gt_one_ge_sixth (μ : Measure Ω) [IsProbabilityMeasure μ]
    (N : Ω → ℝ) (hNm : Measurable N) {H r : ℝ} (hH : 0 ≤ H)
    (hN : ∀ ω, 0 ≤ N ω ∧ N ω ≤ H)
    (hmean : (∫ ω, N ω ∂μ) = r) (hr : 2 ≤ r)
    (hsecond : (∫ ω, N ω ^ 2 ∂μ) ≤ r ^ 2 + r) :
    (1 : ℝ) / 6 ≤ μ.real {ω | 1 < N ω} := by
  let Y : Ω → ℝ := fun ω => max (N ω - 1) 0
  let E : Set Ω := {ω | 1 < N ω}
  let I : Ω → ℝ := E.indicator (fun _ => 1)
  have hE : MeasurableSet E := measurableSet_lt measurable_const hNm
  have hYm : Measurable Y := (hNm.sub measurable_const).max measurable_const
  have hYbounds (ω : Ω) : 0 ≤ Y ω ∧ Y ω ≤ H :=
    ⟨le_max_right _ _, max_le (by linarith [(hN ω).2]) hH⟩
  have hYL2 : MemLp Y 2 μ := MemLp.of_bound hYm.aestronglyMeasurable H
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hYbounds ω).1]; exact (hYbounds ω).2)
  have hIL2 : MemLp I 2 μ := MemLp.of_bound
    (measurable_const.indicator hE).aestronglyMeasurable 1
    (Eventually.of_forall fun ω => by dsimp [I]; by_cases h : ω ∈ E <;> simp [h])
  have hNI : Integrable N μ := Integrable.of_bound hNm.aestronglyMeasurable H
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hN ω).1]; exact (hN ω).2)
  have hNL2 : MemLp N 2 μ := MemLp.of_bound hNm.aestronglyMeasurable H
    (Eventually.of_forall fun ω => by rw [Real.norm_eq_abs, abs_of_nonneg (hN ω).1]; exact (hN ω).2)
  have hYI := hYL2.integrable (by norm_num : (1 : ENNReal) ≤ 2)
  have hEY : r - 1 ≤ ∫ ω, Y ω ∂μ := by
    have h := integral_mono (hNI.sub (integrable_const 1)) hYI (fun ω => le_max_left _ _)
    change (∫ ω, N ω - 1 ∂μ) ≤ (∫ ω, Y ω ∂μ) at h
    rw [integral_sub hNI (integrable_const 1), hmean] at h
    simpa only [integral_const, probReal_univ, one_smul] using h
  have hEY2 : (∫ ω, Y ω ^ 2 ∂μ) ≤ r ^ 2 + r := by
    apply (integral_mono hYL2.integrable_sq hNL2.integrable_sq ?_).trans hsecond
    intro ω
    have hle : Y ω ≤ N ω := max_le (by linarith) (hN ω).1
    exact sq_le_sq₀ (hYbounds ω).1 (hN ω).1 |>.mpr hle
  have hcs := sum_integral_mul_sq_le (ι := Unit) (fun _ => μ) (fun _ => Y) (fun _ => I)
    (fun _ => hYL2) (fun _ => hIL2)
  simp only [Fintype.sum_unique] at hcs
  have hprod : (∫ ω, Y ω * I ω ∂μ) = ∫ ω, Y ω ∂μ := by
    apply integral_congr_ae
    exact Eventually.of_forall fun ω => by
      by_cases h : ω ∈ E
      · simp [I, h]
      · have hny : Y ω = 0 := max_eq_right (by dsimp [E] at h; linarith only [not_lt.mp h])
        simp [I, h, hny]
  have hI2 : (∫ ω, I ω ^ 2 ∂μ) = μ.real E := by
    have heq : (fun ω => I ω ^ 2) = E.indicator (fun _ => (1 : ℝ)) := by
      funext ω
      by_cases h : ω ∈ E <;> simp [I, h]
    rw [heq]
    simpa only [smul_eq_mul, mul_one] using integral_indicator_const (μ := μ) (1 : ℝ) hE
  rw [hprod, hI2] at hcs
  have hq : 0 ≤ μ.real E := measureReal_nonneg
  have hmul := mul_le_mul_of_nonneg_right hEY2 hq
  have hr2 : r ^ 2 + r ≤ (3 / 2 : ℝ) * r ^ 2 := by nlinarith only [hr]
  have hmul2 := mul_le_mul_of_nonneg_right hr2 hq
  have hmain : r ^ 2 / 4 ≤ (3 / 2 : ℝ) * r ^ 2 * μ.real E := by
    nlinarith only [hEY, hr, hcs, hmul, hmul2]
  have hrpos : 0 < r := by linarith only [hr]
  apply (mul_le_mul_iff_right₀ (sq_pos_of_pos hrpos)).mp
  nlinarith only [hmain]

end ProphetSecretary.Analysis
