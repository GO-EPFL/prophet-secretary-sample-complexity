import ProphetSecretary.Limiting.LabeledBandConvergence
import ProphetSecretary.Limiting.FiniteShiftedSum

/-!
# Residual bands for arbitrary chosen finite labels

The padded remainder has the literal filtered aggregate band measure. Its
tail count is bounded by the original total count, and its squared tail sum
is controlled by a uniform residual rarity bound times that total count.
-/
open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma labeledRemainder_band_sum (P : Model.Instance n) (N : ℕ) {b : ℝ} (hb : 0≤b) :
    (∑ i : Fin n, ((labeledRemainder P N).marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi b))=
      labeledBandResidual P N b := by
  let f : ℕ → FiniteMeasure ℝ := fun j => (labeledPaddedLaw P j).toFiniteMeasure.restrict (Ioi b)
  have hf (j : ℕ) (hj : n≤j) : f j=0 := by
    apply FiniteMeasure.toMeasure_injective
    change (labeledPaddedLaw P j : Measure ℝ).restrict (Ioi b)=0
    rw [labeledPaddedLaw_of_ge P hj]
    simp only [restrict_dirac' measurableSet_Ioi,mem_Ioi,not_lt.mpr hb,if_false]
  have hs := shifted_finite_sum_eq_filtered f n N hf
  have hL : (∑ i : Fin n, ((labeledRemainder P N).marginalProbabilityLaw i).toFiniteMeasure.restrict (Ioi b))=
      ∑ j∈Finset.range n, f (N+j) := by
    change (∑ i : Fin n, f (N+i.val))=_
    exact Fin.sum_univ_eq_sum_range (fun j => f (N+j)) n
  rw [hL,hs]
  unfold labeledBandResidual
  rw [Finset.sum_filter]
  have hFin : (∑ i : Fin n, if N≤ i.val then f i.val else 0)=
      ∑ j∈Finset.range n, if N≤j then f j else 0 :=
    Fin.sum_univ_eq_sum_range (fun j => if N≤j then f j else 0) n
  rw [Finset.sum_filter,← hFin]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : N≤ i.val
  · rw [if_pos hi,if_pos hi]
    dsimp only [f]
    rw [labeledPaddedLaw_of_lt P i.isLt]
  · rw [if_neg hi,if_neg hi]

lemma labeledRemainder_tail_sum (P : Model.Instance n) (N : ℕ) {b : ℝ} (hb : 0≤b) :
    (labeledRemainder P N).tailCount b=
      ∑ i∈Finset.univ.filter (fun i : Fin n => N≤ i.val), (P.law i).real (Ioi b) := by
  let f : ℕ → ℝ := fun j => (labeledPaddedLaw P j : Measure ℝ).real (Ioi b)
  have hf (j : ℕ) (hj : n≤j) : f j=0 := by
    dsimp only [f]
    rw [labeledPaddedLaw_of_ge P hj]
    simp [Measure.real,Measure.dirac_apply',not_lt.mpr hb]
  have h := shifted_fin_sum_eq_filtered f n N hf
  change (∑ i : Fin n, f (N+i.val))=_
  rw [h]
  apply Finset.sum_congr rfl
  intro i _
  dsimp only [f]
  rw [labeledPaddedLaw_of_lt P i.isLt]
  rfl

lemma labeledRemainder_tailCount_le (P : Model.Instance n) (N : ℕ) {b : ℝ} (hb : 0≤b) :
    (labeledRemainder P N).tailCount b≤P.tailCount b := by
  rw [labeledRemainder_tail_sum P N hb]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _) (fun _ _ _ => measureReal_nonneg)

lemma labeledRemainder_tail_square_sum_le (P : Model.Instance n) (N : ℕ) {b δ : ℝ} (hb : 0≤b)
    (hRare : ∀ j, N≤j → (labeledPaddedLaw P j : Measure ℝ).real (Ioi b)≤δ) :
    (∑ i : Fin n, ((labeledRemainder P N).law i).real (Ioi b)^2)≤δ*P.tailCount b := by
  have hδ : 0≤δ := (measureReal_nonneg (μ := (labeledPaddedLaw P N : Measure ℝ)) (s := Ioi b)).trans (hRare N le_rfl)
  have hPoint (i : Fin n) : ((labeledRemainder P N).law i).real (Ioi b)^2≤
      δ*((labeledRemainder P N).law i).real (Ioi b) := by
    have h := hRare (N+i.val) (by omega)
    have h0 : 0≤((labeledRemainder P N).law i).real (Ioi b) := measureReal_nonneg
    have h' : ((labeledRemainder P N).law i).real (Ioi b)≤δ := h
    nlinarith only [h',h0]
  calc
    _ ≤ ∑ i : Fin n, δ*((labeledRemainder P N).law i).real (Ioi b) := Finset.sum_le_sum (fun i _ => hPoint i)
    _ = δ*(labeledRemainder P N).tailCount b := by
      change (∑ i : Fin n, δ*((labeledRemainder P N).law i).real (Ioi b))=
        δ*∑ i : Fin n, ((labeledRemainder P N).law i).real (Ioi b)
      rw [Finset.mul_sum]
    _ ≤ δ*P.tailCount b := mul_le_mul_of_nonneg_left (labeledRemainder_tailCount_le P N hb) hδ

end ProphetSecretary.Limiting
