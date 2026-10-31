import ProphetSecretary.Limiting.FiniteShiftedSum
import ProphetSecretary.Model.WeakValueContinuity

/-!
# Actual upper-band intensity of the ordered padded remainder

The finite replaced block has the same band measure as the extracted residual
of the original finite instance. Added zero identities contribute no mass.
-/

open MeasureTheory Set BoundedContinuousFunction
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma weightOrderedRemainder_band_sum (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ)
    {b : ℝ} (hb : 0 ≤ b) :
    (∑ i : Fin n, ((weightOrderedRemainder P w N).marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi b)) =
      weightOrderedBandResidual P w N b := by
  let f : ℕ → FiniteMeasure ℝ := fun j => (weightOrderedPaddedLaw P w j).toFiniteMeasure.restrict (Ioi b)
  have hf (j : ℕ) (hj : n ≤ j) : f j = 0 := by
    apply FiniteMeasure.toMeasure_injective
    change (weightOrderedPaddedLaw P w j : Measure ℝ).restrict (Ioi b) = 0
    rw [weightOrderedPaddedLaw_of_ge P w hj]
    simp only [restrict_dirac' measurableSet_Ioi,mem_Ioi,not_lt.mpr hb,if_false]
  have hs := shifted_finite_sum_eq_filtered f n N hf
  have hL : (∑ i : Fin n, ((weightOrderedRemainder P w N).marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi b)) =
      ∑ j ∈ Finset.range n, f (N+j) := by
    change (∑ i : Fin n, f (N+i.val)) = _
    exact Fin.sum_univ_eq_sum_range (fun j => f (N+j)) n
  rw [hL,hs]
  unfold weightOrderedBandResidual
  rw [Finset.sum_filter]
  have hFin : (∑ i : Fin n, if N ≤ i.val then f i.val else 0) =
      ∑ j ∈ Finset.range n, if N ≤ j then f j else 0 :=
    Fin.sum_univ_eq_sum_range (fun j => if N ≤ j then f j else 0) n
  rw [Finset.sum_filter]
  rw [← hFin]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : N ≤ i.val
  · rw [if_pos hi,if_pos hi]
    dsimp only [f]
    rw [weightOrderedPaddedLaw_of_lt P w i.isLt]
  · rw [if_neg hi,if_neg hi]

lemma weightOrderedRemainder_tail_square_sum (P : Model.Instance n) (w : ℝ →ᵇ ℝ) (N : ℕ)
    {b : ℝ} (hb : 0 ≤ b) :
    (∑ i : Fin n, ((weightOrderedRemainder P w N).law i).real (Ioi b)^2) =
      ∑ i ∈ Finset.univ.filter (fun i : Fin n => N ≤ i.val),
        (weightOrderedPaddedLaw P w i.val : Measure ℝ).real (Ioi b)^2 := by
  let f : ℕ → ℝ := fun j => (weightOrderedPaddedLaw P w j : Measure ℝ).real (Ioi b)^2
  have hf (j : ℕ) (hj : n ≤ j) : f j = 0 := by
    dsimp only [f]
    rw [weightOrderedPaddedLaw_of_ge P w hj]
    simp [Measure.real,Measure.dirac_apply',not_lt.mpr hb]
  exact shifted_fin_sum_eq_filtered f n N hf

end ProphetSecretary.Limiting
