import ProphetSecretary.Probability.LikelihoodTilt

/-!
# Centering a bounded-range observable into a likelihood score

If f takes values in [0,R], subtracting its actual mean and dividing by R
produces a centered score bounded by one. This provides the fixed scaling of
individual-variable scores in `updual:scorelift`.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

noncomputable def centeredRangeScore (μ : Measure Ω) (f : Ω → ℝ) (R : ℝ) (x : Ω) : ℝ :=
  (f x - ∫ y, f y ∂μ) / R

lemma measurable_centeredRangeScore (μ : Measure Ω) {f : Ω → ℝ} (hf : Measurable f) (R : ℝ) :
    Measurable (centeredRangeScore μ f R) := (hf.sub measurable_const).div_const R

lemma integrable_of_range (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {R : ℝ} (hr : ∀ x, f x ∈ Icc (0 : ℝ) R) : Integrable f μ := by
  apply Integrable.of_bound hf.aestronglyMeasurable R
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hr x).1]
    exact (hr x).2

lemma integral_mem_range (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {R : ℝ} (hr : ∀ x, f x ∈ Icc (0 : ℝ) R) :
    (∫ x, f x ∂μ) ∈ Icc (0 : ℝ) R := by
  refine ⟨integral_nonneg (fun x => (hr x).1), ?_⟩
  have hi := integral_mono (integrable_of_range μ hf hr) (integrable_const R) (fun x => (hr x).2)
  simpa only [integral_const, probReal_univ, one_smul] using hi

lemma centeredRangeScore_abs_le_one (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {R : ℝ} (hR : 0 < R) (hr : ∀ x, f x ∈ Icc (0 : ℝ) R) (x : Ω) :
    |centeredRangeScore μ f R x| ≤ 1 := by
  have hm := integral_mem_range μ hf hr
  unfold centeredRangeScore
  rw [abs_div, abs_of_pos hR]
  apply (div_le_one hR).mpr
  apply abs_le.mpr
  constructor <;> linarith [(hr x).1, (hr x).2, hm.1, hm.2]

lemma centeredRangeScore_mean (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : Measurable f) {R : ℝ} (hr : ∀ x, f x ∈ Icc (0 : ℝ) R) :
    (∫ x, centeredRangeScore μ f R x ∂μ) = 0 := by
  unfold centeredRangeScore
  rw [integral_div, integral_sub (integrable_of_range μ hf hr) (integrable_const _)]
  simp only [integral_const, probReal_univ, one_smul, sub_self, zero_div]

/-- The change in centering is uniform over all possible values of the observable. -/
lemma centeredRangeScore_abs_difference (μ ν : Measure Ω) (f : Ω → ℝ) (R : ℝ) (x : Ω) :
    |centeredRangeScore μ f R x - centeredRangeScore ν f R x| =
      |(∫ y, f y ∂μ) - ∫ y, f y ∂ν| / |R| := by
  unfold centeredRangeScore
  have heq : (f x - ∫ y, f y ∂μ) / R - (f x - ∫ y, f y ∂ν) / R =
      -((∫ y, f y ∂μ) - ∫ y, f y ∂ν) / R := by ring
  rw [heq, abs_div, abs_neg]

end ProphetSecretary.Probability
