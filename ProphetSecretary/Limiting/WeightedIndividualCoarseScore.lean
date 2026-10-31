import ProphetSecretary.Limiting.WeightedIndividualScore
import ProphetSecretary.Limiting.WeightedResidualCoarseScore

/-!
# The original individual likelihood score is the coarse score pullback

An absent ordered coordinate is a padded zero. Its score centered under the
zero point mass vanishes at that actual zero value. Thus no nonexistent
distribution is requested or disclosed when transferring the score.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n K : ℕ}

lemma weightedCoarseScore_individual_eq_completeScore (P : Model.Instance n) (wgt : ℝ →ᵇ ℝ)
    (N : ℕ) (hKN : K ≤ N) (i : Fin K) (f : ℝ →ᵇ ℝ) (x : Fin n → ℝ) :
    weightedCoarseScore P wgt N hKN
      (fun y : Fin (K+n) → ℝ => centeredBoundedScore ((weightOrderedPrefix P wgt K).law i) f (y (i.castAdd n))) x=
      completeScore (weightedIndividualScore P wgt i.val f) x := by
  unfold weightedCoarseScore
  change centeredBoundedScore ((weightOrderedPrefix P wgt K).law i) f
    (Model.ZeroSimulation.appendValues (x ∘ weightedMeanPermutation P wgt)
      (weightedCoarseEmbedding n K N hKN (i.castAdd n)))=_
  rw [appendOrderedValues_eq_weightedPaddedValue,weightedCoarseEmbedding_left,weightedIndividualScore_complete]
  by_cases hi : i.val<n
  · rw [dif_pos hi]
    have hLaw : (weightOrderedPrefix P wgt K).law i=P.law (weightedMeanPermutation P wgt ⟨i.val,hi⟩) := by
      change (weightOrderedPaddedLaw P wgt i.val:Measure ℝ)=_
      rw [weightOrderedPaddedLaw_of_lt P wgt hi]
      rfl
    rw [hLaw]
    simp only [weightedPaddedValue,dif_pos hi]
  · rw [dif_neg hi]
    have hLaw : (weightOrderedPrefix P wgt K).law i=Measure.dirac 0 :=
      weightOrderedPaddedLaw_of_ge P wgt (not_lt.mp hi)
    rw [hLaw]
    have hVal : weightedPaddedValue P wgt x i.val=0 := by simp [weightedPaddedValue,hi]
    rw [hVal]
    simp [centeredBoundedScore,centeredRangeScore]
end ProphetSecretary.Limiting
