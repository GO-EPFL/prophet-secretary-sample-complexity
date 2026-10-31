import ProphetSecretary.Probability.CompensatedBandScore

/-!
# Actual laws under complement-compensated band tilts

The mass on B is multiplied by 1+t. Every measurable subset of Bᶜ is
multiplied by the same compensating factor 1−tp/(1−p), even when the law has
no atom at zero. This identifies the finite perturbations in `updual:cloudscore`.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω]

lemma tiltLaw_real_of_score_constant (μ : Measure Ω) [IsProbabilityMeasure μ]
    {h : Ω → ℝ} (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1)
    {θ k : ℝ} (hθ : |θ| ≤ 1 / 4)
    {A : Set Ω} (hA : MeasurableSet A) (hconst : ∀ x ∈ A, h x = k) :
    (tiltLaw μ h θ).real A = (1 + θ * k) * μ.real A := by
  have he := integral_indicator_const (μ := tiltLaw μ h θ) (1 : ℝ) hA
  simp only [smul_eq_mul, mul_one] at he
  rw [← he, integral_tiltLaw hh (tiltFactor_ae_nonnegative hb hθ)]
  calc
    _ = ∫ x, (1 + θ * k) * A.indicator (fun _ : Ω => (1 : ℝ)) x ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => by
        by_cases hx : x ∈ A
        · simp only [tiltFactor, Set.indicator_of_mem hx, hconst x hx]
        · simp only [Set.indicator_of_notMem hx, mul_zero]
    _ = _ := by rw [integral_const_mul, integral_indicator_const 1 hA]; simp only [smul_eq_mul, mul_one]

lemma compensatedBandScore_tilt_band_mass (μ : Measure Ω) [IsProbabilityMeasure μ] {B : Set Ω}
    (hB : MeasurableSet B) (hp : μ.real B ≤ 1 / 2) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) :
    (tiltLaw μ (compensatedBandScore μ B) θ).real B = (1 + θ) * μ.real B := by
  have he := tiltLaw_real_of_score_constant μ (measurable_compensatedBandScore μ hB)
    (Eventually.of_forall (compensatedBandScore_abs_le_one μ hp))
    hθ hB
    (fun x hx => compensatedBandScore_of_mem μ hx)
  simpa only [mul_one] using he

lemma compensatedBandScore_tilt_complement_mass (μ : Measure Ω) [IsProbabilityMeasure μ] {B A : Set Ω}
    (hB : MeasurableSet B) (hp : μ.real B ≤ 1 / 2) {θ : ℝ} (hθ : |θ| ≤ 1 / 4)
    (hA : MeasurableSet A) (hsub : A ⊆ Bᶜ) :
    (tiltLaw μ (compensatedBandScore μ B) θ).real A =
      (1 - θ * (μ.real B / (1 - μ.real B))) * μ.real A := by
  have he := tiltLaw_real_of_score_constant μ (measurable_compensatedBandScore μ hB)
    (Eventually.of_forall (compensatedBandScore_abs_le_one μ hp))
    hθ hA
    (fun x hx => compensatedBandScore_of_notMem μ (hsub hx))
  simpa only [mul_neg, ← sub_eq_add_neg] using he

/-- Exact size of the compensating change on any measurable complement subset. -/
lemma compensatedBandScore_tilt_complement_difference (μ : Measure Ω) [IsProbabilityMeasure μ] {B A : Set Ω}
    (hB : MeasurableSet B) (hp : μ.real B ≤ 1 / 2) {θ : ℝ} (hθ : |θ| ≤ 1 / 4)
    (hA : MeasurableSet A) (hsub : A ⊆ Bᶜ) :
    |(tiltLaw μ (compensatedBandScore μ B) θ).real A - μ.real A| =
      |θ| * (μ.real B / (1 - μ.real B)) * μ.real A := by
  rw [compensatedBandScore_tilt_complement_mass μ hB hp hθ hA hsub]
  have heq : (1 - θ * (μ.real B / (1 - μ.real B))) * μ.real A - μ.real A =
      -(θ * (μ.real B / (1 - μ.real B)) * μ.real A) := by ring
  rw [heq, abs_neg, abs_mul, abs_mul, abs_of_nonneg
    (div_nonneg measureReal_nonneg (by linarith : 0 ≤ 1 - μ.real B)), abs_of_nonneg measureReal_nonneg]

end ProphetSecretary.Probability
