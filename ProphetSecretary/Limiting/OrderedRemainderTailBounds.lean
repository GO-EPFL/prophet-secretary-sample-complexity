import ProphetSecretary.Limiting.WeightedRemainderBand
import ProphetSecretary.Limiting.OrderedResidualTailSup

/-!
# Uniform tail bounds for the actual ordered padded residual block

Every residual variable is bounded by the deterministic residual tail
supremum. Above a nonnegative level, padded zeros contribute no mass, and
the residual expected tail count is at most the original instance's count.
-/
open MeasureTheory Set BoundedContinuousFunction
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma weightOrderedRemainder_tail_le_sup (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ) (d : ℝ) (i : Fin n) :
    ((weightOrderedRemainder P w N).law i).real (Ioi d)≤
      residualTailSup (fun j => weightOrderedPaddedLaw P w j) N d := by
  exact tail_le_residualTailSup (fun j => weightOrderedPaddedLaw P w j) N d (N+i.val) (Nat.le_add_right N i.val)

lemma weightOrderedRemainder_tailCount_le (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ) {d : ℝ} (hd : 0≤d) :
    (weightOrderedRemainder P w N).tailCount d≤P.tailCount d := by
  let f : ℕ → ℝ := fun j => (weightOrderedPaddedLaw P w j:Measure ℝ).real (Ioi d)
  have hf (j : ℕ) (hj : n ≤ j) : f j=0 := by
    dsimp [f]
    rw [weightOrderedPaddedLaw_of_ge P w hj]
    simp [Measure.real,Measure.dirac_apply',not_lt.mpr hd]
  have hShift := shifted_fin_sum_eq_filtered f n N hf
  have hSorted : (∑ i : Fin n, f i.val)=P.tailCount d := by
    have hF (i : Fin n) : f i.val=(P.law (weightedMeanPermutation P w i)).real (Ioi d) := by
      dsimp [f]
      rw [weightOrderedPaddedLaw_of_lt P w i.isLt]
      rfl
    simp only [hF]
    exact Equiv.sum_comp (weightedMeanPermutation P w) (fun i : Fin n => (P.law i).real (Ioi d))
  calc
    _ = ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val), f i.val := hShift
    _ ≤ ∑ i : Fin n, f i.val := Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => measureReal_nonneg)
    _ = _ := hSorted
end ProphetSecretary.Limiting
