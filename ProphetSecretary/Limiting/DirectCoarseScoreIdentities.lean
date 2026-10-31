import ProphetSecretary.Limiting.DirectCoarsePolicy
import ProphetSecretary.Limiting.DirectVirtualScore
import ProphetSecretary.Probability.IndividualScoreLift

/-!
# Complete score pullbacks for direct coarse policies

The complete cloud score retains every virtual coordinate, including values
arriving after stopping. A retained individual's score uses the same actual
marginal and identity in both executions. Neither score is policy input.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {K n N : ℕ}

lemma directCoarseScore_cloud_pullback (hKn : K≤n) (κ : Measure ℝ) (B : Set ℝ) (x : Fin (n+N) → ℝ) :
    completeScore (fun _ : Fin N => bandScore κ B)
      (fun j => (x ∘ directCoarseEmbedding K n N hKn) (j.natAdd K))=
      completeScore (directCloudScore n N κ B) x := by
  rw [directCloudScore_complete]
  simp only [Function.comp_def,directCoarseEmbedding_right]

lemma directCoarseScore_individual_pullback (P : Model.Instance n) (Q : Model.Instance N) (hKn : K≤n)
    (i : Fin K) (f : ℝ →ᵇ ℝ) (x : Fin (n+N) → ℝ) :
    centeredBoundedScore ((P.restrictBy (Fin.castLEEmb hKn)).law i) f
      ((x ∘ directCoarseEmbedding K n N hKn) (i.castAdd N))=
      completeScore (individualContinuousScore (P.appendIndependent Q).law ((Fin.castLE hKn i).castAdd N) f) x := by
  rw [individualContinuousScore_complete]
  simp only [Function.comp_def,directCoarseEmbedding_left,Model.Instance.appendIndependent_law_left]
  rfl
end ProphetSecretary.Limiting
