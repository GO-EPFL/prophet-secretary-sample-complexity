import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Probability.IndividualScoreLift

/-!
# Retained-individual likelihood scores in direct finite approximations

The fixed natural individual index is scored only when it is present in the
retained prefix. Otherwise every coordinate score is zero. Centering uses
its actual retained marginal; the common bounded-continuous scale is fixed.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n N : ℕ}

noncomputable def directIndividualScore (P : Model.Instance n) (Q : Model.Instance N) (i : ℕ)
    (f : ℝ →ᵇ ℝ) : Fin (n+N) → ℝ → ℝ :=
  if hi : i<n then individualContinuousScore (P.appendIndependent Q).law ((⟨i,hi⟩:Fin n).castAdd N) f else fun _ _ => 0

lemma directIndividualScore_properties (P : Model.Instance n) (Q : Model.Instance N) (i : ℕ) (f : ℝ →ᵇ ℝ) :
    (∀ j, Measurable (directIndividualScore P Q i f j)) ∧
      (∀ j x, |directIndividualScore P Q i f j x|≤1) ∧
      (∀ j, (∫ x, directIndividualScore P Q i f j x ∂(P.appendIndependent Q).law j)=0) ∧
      information (P.appendIndependent Q).law (directIndividualScore P Q i f)≤1 := by
  unfold directIndividualScore
  by_cases hi : i<n
  · rw [dif_pos hi]
    refine ⟨individualContinuousScore_measurable (P.appendIndependent Q).law _ f,?_,
      individualContinuousScore_centered (P.appendIndependent Q).law _ f,
      individualContinuousScore_information_le_one (P.appendIndependent Q).law _ f⟩
    intro j x
    unfold individualContinuousScore singleScore
    by_cases hj : j=((⟨i,hi⟩:Fin n).castAdd N)
    · subst j
      simp only [if_true]
      exact centeredBoundedScore_abs_le_one _ f x
    · simp only [if_neg hj,abs_zero,zero_le_one]
  · rw [dif_neg hi]
    refine ⟨(fun _ => measurable_const),(fun _ _ => by norm_num),(fun _ => by simp),?_⟩
    simp only [information,zero_pow (by norm_num : (2:ℕ)≠0),integral_zero,Finset.sum_const_zero,zero_le_one]

lemma directIndividualScore_complete (P : Model.Instance n) (Q : Model.Instance N) (i : ℕ) (f : ℝ →ᵇ ℝ)
    (x : Fin (n+N) → ℝ) :
    completeScore (directIndividualScore P Q i f) x=
      if hi : i<n then centeredBoundedScore (P.law ⟨i,hi⟩) f (x ((⟨i,hi⟩:Fin n).castAdd N)) else 0 := by
  unfold directIndividualScore
  by_cases hi : i<n
  · rw [dif_pos hi,dif_pos hi,individualContinuousScore_complete,Model.Instance.appendIndependent_law_left]
  · rw [dif_neg hi,dif_neg hi]
    simp only [completeScore,Finset.sum_const_zero]
end ProphetSecretary.Limiting
