import ProphetSecretary.Limiting.WeightedOrdering
import ProphetSecretary.Probability.IndividualScoreLift

/-!
# Finite original-coordinate scores for one limiting individual

The fixed ordered individual is scored when it exists in the finite array.
Otherwise the score is zero. Centering uses the actual original marginal;
the global scale depends only on the fixed bounded continuous observable.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def weightedIndividualScore (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (j : ℕ)
    (f : ℝ →ᵇ ℝ) : Fin n → ℝ → ℝ :=
  if hj : j<n then individualContinuousScore P.law (weightedMeanPermutation P wgt ⟨j,hj⟩) f else fun _ _ => 0

lemma weightedIndividualScore_properties (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (j : ℕ) (f : ℝ →ᵇ ℝ) :
    (∀ i, Measurable (weightedIndividualScore P wgt j f i)) ∧
      (∀ i x, |weightedIndividualScore P wgt j f i x|≤1) ∧
      (∀ i, (∫ x, weightedIndividualScore P wgt j f i x ∂P.law i)=0) ∧
      information P.law (weightedIndividualScore P wgt j f)≤1 := by
  unfold weightedIndividualScore
  by_cases hj : j<n
  · rw [dif_pos hj]
    refine ⟨individualContinuousScore_measurable P.law _ f,?_,individualContinuousScore_centered P.law _ f,
      individualContinuousScore_information_le_one P.law _ f⟩
    intro i x
    unfold individualContinuousScore singleScore
    by_cases hi : i=weightedMeanPermutation P wgt ⟨j,hj⟩
    · subst i
      simp only [if_true]
      exact centeredBoundedScore_abs_le_one _ f x
    · simp only [if_neg hi,abs_zero,zero_le_one]
  · rw [dif_neg hj]
    refine ⟨(fun _ => measurable_const),(fun _ _ => by norm_num),(fun _ => by simp),?_⟩
    simp only [information,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero,Finset.sum_const_zero,zero_le_one]

lemma weightedIndividualScore_complete (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ) (j : ℕ) (f : ℝ →ᵇ ℝ)
    (x : Fin n → ℝ) :
    completeScore (weightedIndividualScore P wgt j f) x=
      if hj : j<n then centeredBoundedScore (P.law (weightedMeanPermutation P wgt ⟨j,hj⟩)) f
        (x (weightedMeanPermutation P wgt ⟨j,hj⟩)) else 0 := by
  unfold weightedIndividualScore
  by_cases hj : j<n
  · rw [dif_pos hj,dif_pos hj]
    exact individualContinuousScore_complete P.law _ f x
  · rw [dif_neg hj,dif_neg hj]
    simp [completeScore]
end ProphetSecretary.Limiting
