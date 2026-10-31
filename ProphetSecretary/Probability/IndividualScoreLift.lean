import ProphetSecretary.Probability.CenteredBoundedScore
import ProphetSecretary.Probability.CenteredValueScore
import ProphetSecretary.Probability.SingleMarginalTilt

/-!
# Lifting one continuous individual score into a finite product

Only the designated coordinate carries the centered observable. Every other
coordinate has score zero, so the complete-vector score and information are
exactly those of that marginal, uniformly in the number of offers. This is the
finite individual-score construction in `updual:scorelift`.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical BigOperators

namespace ProphetSecretary.Probability

variable {n : ℕ}

lemma singleScore_information (μ : Fin n → Measure ℝ) (j : Fin n) (h : ℝ → ℝ) :
    information μ (singleScore j h) = ∫ x, h x ^ 2 ∂μ j := by
  unfold information
  rw [Finset.sum_eq_single j]
  · simp only [singleScore, if_true]
  · intro i _ hij
    simp only [singleScore, if_neg hij, zero_pow (by norm_num : 2 ≠ 0), integral_zero]
  · simp

noncomputable def individualContinuousScore (μ : Fin n → Measure ℝ) (j : Fin n)
    (f : ℝ →ᵇ ℝ) : Fin n → ℝ → ℝ := singleScore j (centeredBoundedScore (μ j) f)

lemma individualContinuousScore_measurable (μ : Fin n → Measure ℝ) (j : Fin n) (f : ℝ →ᵇ ℝ) (i : Fin n) :
    Measurable (individualContinuousScore μ j f i) :=
  singleScore_measurable j (continuous_centeredBoundedScore (μ j) f).measurable i

lemma individualContinuousScore_centered (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : Fin n) (f : ℝ →ᵇ ℝ) (i : Fin n) :
    (∫ x, individualContinuousScore μ j f i x ∂μ i) = 0 :=
  singleScore_centered μ j (centeredBoundedScore_mean (μ j) f) i

lemma individualContinuousScore_bound (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (j : Fin n) (f : ℝ →ᵇ ℝ) (i : Fin n) :
    ∀ᵐ x ∂μ i, |individualContinuousScore μ j f i x| ≤ 1 :=
  singleScore_bound μ j (Eventually.of_forall (centeredBoundedScore_abs_le_one (μ j) f)) i

lemma individualContinuousScore_complete (μ : Fin n → Measure ℝ) (j : Fin n) (f : ℝ →ᵇ ℝ)
    (x : Fin n → ℝ) :
    completeScore (individualContinuousScore μ j f) x = centeredBoundedScore (μ j) f (x j) :=
  singleScore_complete j _ x

/-- Uniform information bound independent of the finite instance size. -/
lemma individualContinuousScore_information_le_one (μ : Fin n → Measure ℝ)
    [∀ i, IsProbabilityMeasure (μ i)] (j : Fin n) (f : ℝ →ᵇ ℝ) :
    information μ (individualContinuousScore μ j f) ≤ 1 := by
  unfold individualContinuousScore
  rw [singleScore_information]
  exact centeredBoundedScore_secondMoment_le_one (μ j) f

end ProphetSecretary.Probability
