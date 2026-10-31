import ProphetSecretary.Probability.AntitoneCovariance
import ProphetSecretary.Probability.CenteredValueScore

/-!
# Strict covariance for the bounded continuous individual-value score

The globally clipped and centered score agrees on the offer support with
(x−EX)/H. Hence the strict antitone covariance result applies to the actual
bounded continuous score used in `updual:scorelift`.
-/
open MeasureTheory Set Filter
open scoped NNReal
namespace ProphetSecretary.Probability

lemma centeredValueScore_response_eq_covariance (μ : Measure ℝ) {H : ℝ≥0}
    (hX : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) H) (g : ℝ → ℝ) :
    (∫ x, centeredValueScore μ H x * g x ∂μ) = valueCovariance μ g / (H : ℝ) := by
  calc
    _ = ∫ x, ((x - ∫ y, y ∂μ) / (H : ℝ)) * g x ∂μ :=
      integral_congr_ae (hX.mono fun x hx => by dsimp only; rw [centeredValueScore_eq_on_support μ hX hx])
    _ = _ := by
      have heq : (fun x : ℝ => ((x - ∫ y, y ∂μ) / (H : ℝ)) * g x) =
          fun x => ((x - ∫ y, y ∂μ) * g x) / (H : ℝ) := by funext x; ring
      rw [heq,integral_div]
      rfl

/-- Actual continuous bounded-score specialization; no antitonicity is
claimed here for any policy whose conditional response has not been proved
antitone separately. -/
theorem centeredValueScore_response_negative (μ : Measure ℝ) [IsProbabilityMeasure μ]
    {H : ℝ≥0} (hH : 0 < (H : ℝ)) (hX : ∀ᵐ x ∂μ, x ∈ Icc (0 : ℝ) H)
    (g : ℝ → ℝ) (hgm : Measurable g) (hgB : ∀ᵐ x ∂μ, g x ∈ Icc (0 : ℝ) 1)
    (hga : Antitone g) (hn : ¬∃ c : ℝ, g =ᵐ[μ] fun _ => c) :
    (∫ x, centeredValueScore μ H x * g x ∂μ) < 0 := by
  rw [centeredValueScore_response_eq_covariance μ hX g]
  exact div_neg_of_neg_of_pos (valueCovariance_negative_of_not_ae_constant μ hX g hgm hgB hga hn) hH

end ProphetSecretary.Probability
