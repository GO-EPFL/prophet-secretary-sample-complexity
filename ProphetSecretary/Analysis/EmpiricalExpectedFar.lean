import ProphetSecretary.Analysis.EmpiricalExpectedNear

/-!
# Averaging the far-below-threshold loss

A window of size Dx and a disagreement error at least x/2 give the explicit
rate 64 D C₆ max(A³,1) x/k from the sixth-moment profile at level Ax.
The conclusion includes integrability of the nonnegative loss.
-/

open MeasureTheory Filter

namespace ProphetSecretary.Analysis

theorem empirical_expected_far_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F E : Ω → ℝ} (hm : AEStronglyMeasurable F μ) (hF0 : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hE : Measurable E) (hE0 : ∀ᵐ ω ∂μ, 0 ≤ E ω) (hI : Integrable (fun ω => E ω ^ 6) μ)
    {k x A D C₆ : ℝ} (hk : 0 < k) (hxk : 1 / k ≤ x) (hD : 0 ≤ D) (hC₆ : 0 ≤ C₆)
    (hdom : ∀ᵐ ω ∂μ, F ω ≤ (D * x) * (if x / 2 ≤ E ω then E ω else 0))
    (hmoment : (∫ ω, E ω ^ 6 ∂μ) ≤ C₆ * (A ^ 3 * x ^ 3 / k ^ 3 + 1 / k ^ 6)) :
    Integrable F μ ∧ (∫ ω, F ω ∂μ) ≤ (64 * D * C₆ * max (A ^ 3) 1) * x / k := by
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have htail := integral_pow_tail_le_higherMoment μ hE hE0 (by positivity : 0 < x / 2)
    (by decide : (1 : ℕ) ≤ 6) hI
  simp only [pow_one] at htail
  have hbase := integral_nonnegative_le_scaled μ hm hF0 htail.1 hdom
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  have hnonneg : 0 ≤ D * x := mul_nonneg hD hx.le
  have hscaled := mul_le_mul_of_nonneg_left htail.2 hnonneg
  have hmom := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hmoment (by positivity : 0 ≤ (x / 2) ^ 5)) hnonneg
  have heq : (D * x) * (C₆ * (A ^ 3 * x ^ 3 / k ^ 3 + 1 / k ^ 6) / (x / 2) ^ 5) =
      32 * D * C₆ * (A ^ 3 * (1 / (x * k ^ 3)) + 1 / (x ^ 4 * k ^ 6)) := by
    field_simp
    ring
  rw [heq] at hmom
  have hM1 := le_max_left (A ^ 3) (1 : ℝ)
  have hM2 := le_max_right (A ^ 3) (1 : ℝ)
  have hfirst := mul_le_mul_of_nonneg_right hM1 (by positivity : 0 ≤ 1 / (x * k ^ 3))
  have hsecond := mul_le_mul_of_nonneg_right hM2 (by positivity : 0 ≤ 1 / (x ^ 4 * k ^ 6))
  have hsum : A ^ 3 * (1 / (x * k ^ 3)) + 1 / (x ^ 4 * k ^ 6) ≤
      max (A ^ 3) 1 * (1 / (x * k ^ 3) + 1 / (x ^ 4 * k ^ 6)) := by
    nlinarith only [hfirst, hsecond]
  have hM0 : 0 ≤ max (A ^ 3) 1 := zero_le_one.trans hM2
  have hrate := mul_le_mul_of_nonneg_left (empirical_far_terms_le hk hxk) hM0
  have hcoef : 0 ≤ 32 * D * C₆ := by positivity
  have hupper := mul_le_mul_of_nonneg_left (hsum.trans hrate) hcoef
  have hfinal := (hscaled.trans hmom).trans hupper
  have hend : (32 * D * C₆) * (max (A ^ 3) 1 * (2 * x / k)) =
      (64 * D * C₆ * max (A ^ 3) 1) * x / k := by ring
  exact hfinal.trans_eq hend

end ProphetSecretary.Analysis
