import ProphetSecretary.Limiting.LabeledRemainderBand
import ProphetSecretary.Limiting.LabeledResidualConsistency

/-!
# Countable sums of the actual zero-padded finite marginal tails

Above a nonnegative level, padded zero laws contribute no mass. Finite
residuals can therefore be compared across different finite dimensions by
their chosen padded tail labels. The countable sums are exact finite sums.
-/
open MeasureTheory Set Filter
open scoped Classical Topology ENNReal BigOperators
namespace ProphetSecretary.Limiting

lemma labeledBandResidual_toMeasure_sum {n : ℕ} (P : Model.Instance n) (N : ℕ)
    {b : ℝ} (hb : 0≤b) :
    (labeledBandResidual P N b : Measure ℝ)=
      Measure.sum (fun j : ℕ => (labeledPaddedLaw P (N+j) : Measure ℝ).restrict (Ioi b)) := by
  rw [← labeledRemainder_band_sum P N hb,FiniteMeasure.toMeasure_sum]
  ext S hS
  rw [Measure.finsetSum_apply,Measure.sum_apply _ hS]
  let f := fun j : ℕ => ((labeledPaddedLaw P (N+j) : Measure ℝ).restrict (Ioi b)) S
  change (∑ i : Fin n, f i.val)=∑' j, f j
  rw [Fin.sum_univ_eq_sum_range f n]
  symm
  apply tsum_eq_sum
  intro j hj
  have hjn : n≤j := by simpa only [Finset.mem_range,not_lt] using hj
  dsimp only [f]
  rw [labeledPaddedLaw_of_ge P (hjn.trans (Nat.le_add_left j N))]
  simp only [restrict_dirac' measurableSet_Ioi,mem_Ioi,not_lt.mpr hb,if_false]
  rfl

lemma labeledBandResidual_eq_of_padded_tail_eq {n m : ℕ} (P : Model.Instance n) (Q : Model.Instance m)
    (N : ℕ) {b : ℝ} (hb : 0≤b)
    (hTail : ∀ j, N≤j → labeledPaddedLaw P j=labeledPaddedLaw Q j) :
    labeledBandResidual P N b=labeledBandResidual Q N b := by
  apply FiniteMeasure.toMeasure_injective
  rw [labeledBandResidual_toMeasure_sum P N hb,labeledBandResidual_toMeasure_sum Q N hb]
  apply congrArg Measure.sum
  funext j
  rw [hTail (N+j) (Nat.le_add_right N j)]

lemma extendedTailCount_eq_padded_tsum {n : ℕ} (P : Model.Instance n) {b : ℝ} (hb : 0≤b) :
    extendedTailCount P b=∑' j : ℕ, (labeledPaddedLaw P j : Measure ℝ) (Ioi b) := by
  have hEq : (∑ j∈Finset.range n, (labeledPaddedLaw P j : Measure ℝ) (Ioi b))=extendedTailCount P b := by
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    rw [labeledPaddedLaw_of_lt P i.isLt]
    rfl
  rw [← hEq]
  symm
  apply tsum_eq_sum
  intro j hj
  have hjn : n≤j := by simpa only [Finset.mem_range,not_lt] using hj
  rw [labeledPaddedLaw_of_ge P hjn]
  simp [Measure.dirac_apply',not_lt.mpr hb]

lemma labeledBandResidual_prefix {n : ℕ} (P : Model.Instance n) (N k : ℕ) {b : ℝ} (hb : 0≤b) :
    labeledBandResidual P N b=
      (∑ j∈Finset.range k, (labeledPaddedLaw P (N+j)).toFiniteMeasure.restrict (Ioi b))+
        labeledBandResidual P (N+k) b := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ,add_assoc,show N+(k+1)=N+k+1 by omega,
      ← labeledBandResidual_succ P (N+k) hb]
    exact ih

end ProphetSecretary.Limiting
