import Mathlib.MeasureTheory.Function.L2Space

/-!
# Second moments of a score times a bounded payoff

The score is an arbitrary square-integrable analytical random variable. A
bounded payoff multiplies its second moment by at most the squared bound;
no independence between the score and payoff is required.
-/
open MeasureTheory Filter
namespace ProphetSecretary.Probability
variable {Ω : Type*} [MeasurableSpace Ω]

lemma bounded_score_payoff_memLp_and_secondMoment (μ : Measure Ω)
    (s g : Ω → ℝ) (hs : MemLp s 2 μ) (hg : AEStronglyMeasurable g μ)
    {I D : ℝ} (hI : (∫ q, (s q)^2 ∂μ)≤I) (_hD : 0≤D)
    (hb : ∀ᵐ q ∂μ, |g q|≤D) :
    MemLp (fun q => s q*g q) 2 μ ∧ (∫ q, (s q*g q)^2 ∂μ)≤D^2*I := by
  have hProd : MemLp (fun q => s q*g q) 2 μ := (hs.abs.const_mul D).mono'
    (hs.aestronglyMeasurable.mul hg) (by
      filter_upwards [hb] with q hq
      change |s q*g q|≤D*|s q|
      rw [abs_mul]
      simpa only [mul_comm] using mul_le_mul_of_nonneg_left hq (abs_nonneg (s q)))
  refine ⟨hProd,?_⟩
  have hs2 := (memLp_two_iff_integrable_sq hs.aestronglyMeasurable).mp hs
  have hProd2 := (memLp_two_iff_integrable_sq hProd.aestronglyMeasurable).mp hProd
  calc
    _ ≤ ∫ q, D^2*(s q)^2 ∂μ := by
      apply integral_mono_ae hProd2 (hs2.const_mul (D^2))
      filter_upwards [hb] with q hq
      have hqSq : (g q)^2≤D^2 := by
        have hBounds := abs_le.mp hq
        nlinarith
      simpa only [mul_pow,mul_comm] using mul_le_mul_of_nonneg_left hqSq (sq_nonneg (s q))
    _ = D^2*(∫ q, (s q)^2 ∂μ) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left hI (sq_nonneg D)
end ProphetSecretary.Probability
