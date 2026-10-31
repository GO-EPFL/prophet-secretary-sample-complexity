import ProphetSecretary.Probability.LikelihoodTilt

/-!
# Band scores compensated on the full complement

The score is 1 on B and −p/(1−p) on its complement, where p=μ(B).
This is `updual:cloudscore`; unlike compensation at zero, it applies to laws
without any zero atom. Scores of the complete offer vector remain analytical.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def compensatedBandScore (μ : Measure Ω) (B : Set Ω) (x : Ω) : ℝ :=
  B.indicator (fun _ => 1) x - (μ.real B / (1 - μ.real B)) * Bᶜ.indicator (fun _ => 1) x

lemma measurable_compensatedBandScore (μ : Measure Ω) {B : Set Ω} (hB : MeasurableSet B) :
    Measurable (compensatedBandScore μ B) :=
  (measurable_const.indicator hB).sub (measurable_const.mul (measurable_const.indicator hB.compl))

lemma compensatedBandScore_of_mem (μ : Measure Ω) {B : Set Ω} {x : Ω} (hx : x ∈ B) :
    compensatedBandScore μ B x = 1 := by simp [compensatedBandScore, hx]

lemma compensatedBandScore_of_notMem (μ : Measure Ω) {B : Set Ω} {x : Ω} (hx : x ∉ B) :
    compensatedBandScore μ B x = -(μ.real B / (1 - μ.real B)) := by simp [compensatedBandScore, hx]

lemma compensatedBandScore_normalized (μ : Measure Ω) {B : Set Ω}
    (hp : μ.real B ≠ 1) (x : Ω) :
    compensatedBandScore μ B x = (B.indicator (fun _ => (1 : ℝ)) x - μ.real B) / (1 - μ.real B) := by
  have hq : 1 - μ.real B ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  by_cases hx : x ∈ B
  · rw [compensatedBandScore_of_mem μ hx, Set.indicator_of_mem hx]
    exact (div_self hq).symm
  · rw [compensatedBandScore_of_notMem μ hx, Set.indicator_of_notMem hx]
    ring

lemma compensatedBandScore_abs_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Set Ω}
    (hp : μ.real B ≤ 1 / 2) (x : Ω) : |compensatedBandScore μ B x| ≤ 1 := by
  have hp0 : 0 ≤ μ.real B := measureReal_nonneg
  have hq : 0 < 1 - μ.real B := by linarith
  by_cases hx : x ∈ B
  · rw [compensatedBandScore_of_mem μ hx]
    norm_num
  · rw [compensatedBandScore_of_notMem μ hx, abs_neg, abs_of_nonneg (div_nonneg hp0 hq.le)]
    apply (div_le_one hq).mpr
    linarith only [hp]

lemma compensatedBandScore_mean (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Set Ω}
    (hB : MeasurableSet B) (hp : μ.real B < 1) :
    (∫ x, compensatedBandScore μ B x ∂μ) = 0 := by
  have hq : 1 - μ.real B ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hiB : Integrable (B.indicator (fun _ : Ω => (1 : ℝ))) μ := (integrable_const 1).indicator hB
  have hiC : Integrable (Bᶜ.indicator (fun _ : Ω => (1 : ℝ))) μ := (integrable_const 1).indicator hB.compl
  unfold compensatedBandScore
  rw [integral_sub hiB (hiC.const_mul _), integral_const_mul,
    integral_indicator_const 1 hB, integral_indicator_const 1 hB.compl,
    measureReal_compl hB, probReal_univ]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

lemma compensatedBandScore_sq (μ : Measure Ω) (B : Set Ω) (x : Ω) :
    compensatedBandScore μ B x ^ 2 = B.indicator (fun _ => (1 : ℝ)) x +
      (μ.real B / (1 - μ.real B)) ^ 2 * Bᶜ.indicator (fun _ => (1 : ℝ)) x := by
  by_cases hx : x ∈ B
  · simp [compensatedBandScore_of_mem μ hx, hx]
  · simp [compensatedBandScore_of_notMem μ hx, hx]

lemma compensatedBandScore_secondMoment (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Set Ω}
    (hB : MeasurableSet B) (hp : μ.real B < 1) :
    (∫ x, compensatedBandScore μ B x ^ 2 ∂μ) = μ.real B / (1 - μ.real B) := by
  have hq : 1 - μ.real B ≠ 0 := ne_of_gt (sub_pos.mpr hp)
  have hiB : Integrable (B.indicator (fun _ : Ω => (1 : ℝ))) μ := (integrable_const 1).indicator hB
  have hiC : Integrable (Bᶜ.indicator (fun _ : Ω => (1 : ℝ))) μ := (integrable_const 1).indicator hB.compl
  simp_rw [compensatedBandScore_sq μ B]
  rw [integral_add hiB (hiC.const_mul _), integral_const_mul,
    integral_indicator_const 1 hB, integral_indicator_const 1 hB.compl,
    measureReal_compl hB, probReal_univ]
  simp only [smul_eq_mul, mul_one]
  field_simp
  ring

lemma compensatedBandScore_secondMoment_le (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Set Ω}
    (hB : MeasurableSet B) (hp : μ.real B ≤ 1 / 2) :
    (∫ x, compensatedBandScore μ B x ^ 2 ∂μ) ≤ 2 * μ.real B := by
  rw [compensatedBandScore_secondMoment μ hB (by linarith only [hp])]
  have hp0 : 0 ≤ μ.real B := measureReal_nonneg
  apply (div_le_iff₀ (by linarith : 0 < 1 - μ.real B)).mpr
  nlinarith only [hp, hp0]

/-- The difference from the centered band count is a small multiple of the score. -/
lemma compensatedBandScore_centered_difference (μ : Measure Ω) {B : Set Ω}
    (hp : μ.real B ≠ 1) (x : Ω) :
    compensatedBandScore μ B x - (B.indicator (fun _ => (1 : ℝ)) x - μ.real B) =
      μ.real B * compensatedBandScore μ B x := by
  rw [compensatedBandScore_normalized μ hp]
  have hq : 1 - μ.real B ≠ 0 := sub_ne_zero.mpr (Ne.symm hp)
  field_simp
  ring

end ProphetSecretary.Probability
