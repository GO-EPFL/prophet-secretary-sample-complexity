import ProphetSecretary.Probability.NormalizedScoreResponse
import ProphetSecretary.Probability.CenteredBoundedScore

/-!
# Fixed scalar rescaling of complete analytical scores

The unit normalization used in likelihood estimates loses no bounded
continuous score: multiplication by the fixed positive scale recovers the
literal centered observable. Reward, duration and maximum covariances are
linear in that score, before any limiting operation.
-/
open MeasureTheory BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Probability

lemma completeScore_const_mul {n : ℕ} (a : ℝ) (h : Fin n → ℝ → ℝ) (x : Fin n → ℝ) :
    completeScore (fun i y => a*h i y) x=a*completeScore h x := by
  simp only [completeScore,Finset.mul_sum]

lemma boundedScoreScale_mul_centeredBoundedScore (μ : Measure ℝ) (f : ℝ →ᵇ ℝ) (x : ℝ) :
    boundedScoreScale f*centeredBoundedScore μ f x=f x-∫ y, f y ∂μ := by
  change boundedScoreScale f*((f x-∫ y, f y ∂μ)/boundedScoreScale f)=_
  exact mul_div_cancel₀ _ (boundedScoreScale_positive f).ne'

end ProphetSecretary.Probability
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma RandomizedPolicy.expectedRewardScore_const_mul (π : RandomizedPolicy n) (P : Instance n)
    (a : ℝ) (h : Fin n → ℝ → ℝ) :
    π.expectedRewardScore P (fun i x => a*h i x)=a*π.expectedRewardScore P h := by
  unfold expectedRewardScore
  simp only [completeScore_const_mul,mul_assoc,integral_const_mul]

lemma RandomizedPolicy.expectedDurationScore_const_mul (π : RandomizedPolicy n) (P : Instance n)
    (a : ℝ) (h : Fin n → ℝ → ℝ) :
    π.expectedDurationScore P (fun i x => a*h i x)=a*π.expectedDurationScore P h := by
  unfold expectedDurationScore
  simp only [completeScore_const_mul,mul_assoc,integral_const_mul]

lemma Instance.expectedMaximumScore_const_mul (P : Instance n) (a : ℝ) (h : Fin n → ℝ → ℝ) :
    P.expectedMaximumScore (fun i x => a*h i x)=a*P.expectedMaximumScore h := by
  unfold expectedMaximumScore
  simp only [completeScore_const_mul,mul_assoc,integral_const_mul]
end ProphetSecretary.Model
