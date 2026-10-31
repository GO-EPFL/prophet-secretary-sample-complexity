import ProphetSecretary.Limiting.ChronologicalHistoryRank

/-!
# The chronological tags of the actual finite observed history

A tie-free array has one simultaneous identity for every observation time:
constructing tags from the observed past measure equals retaining the past
points of the independently tagged array. The array description is analytical;
the implemented observation uses only the past measure and auxiliary sequence.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

noncomputable def chronologicalObservedTagHistory {T : Type*} [MeasurableSpace T]
    (ω : Configuration) (σ : ℕ → T) (t : ℝ) : Measure (ℝ × (ℝ × T)) :=
  ∑ j : Fin ω.1, if (ω.2 j).1<t then
    Measure.dirac ((ω.2 j).1,((ω.2 j).2,σ (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val)) else 0

lemma chronologicalTaggedHistory_eq_array_past {T : Type*} [MeasurableSpace T]
    (ω : Configuration) (σ : ℕ → T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) (t : ℝ) :
    chronologicalTaggedHistory σ (observedFiniteHistory ω t)=chronologicalObservedTagHistory ω σ t := by
  let g := tagPointByFiniteHistory σ (observedFiniteHistory ω t)
  have hG : Measurable g := by
    change Measurable (fun p : Point => tagPointByFiniteHistory σ (observedFiniteHistory ω t) p)
    exact (measurable_tagPointByFiniteHistory (T := T)).comp
      ((measurable_const (a := (σ,observedFiniteHistory ω t))).prodMk measurable_id)
  ext S hS
  change ((observedFiniteHistory ω t : Measure Point).map g) S=chronologicalObservedTagHistory ω σ t S
  rw [Measure.map_apply hG hS,observedFiniteHistory_coe]
  simp only [observedHistory,chronologicalObservedTagHistory,Measure.coe_finsetSum,Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (ω.2 j).1<t
  · rw [if_pos hj,if_pos hj,Measure.dirac_apply' _ (hS.preimage hG),Measure.dirac_apply' _ hS]
    have hRank := finitePastRank_observedHistory ω hClock j hj.le
    have hPoint : g (ω.2 j)=((ω.2 j).1,((ω.2 j).2,σ (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val)) := by
      change ((ω.2 j).1,((ω.2 j).2,σ (finitePastRank (observedFiniteHistory ω t) (ω.2 j).1)))=_
      rw [hRank]
    change (if g (ω.2 j)∈S then (1 : ℝ≥0∞) else 0)=_
    rw [hPoint]
    simp only [Set.indicator_apply,Pi.one_apply]
  · simp only [if_neg hj]
    rfl

lemma chronological_currentTag_eq_rank {T : Type*} (ω : Configuration) (σ : ℕ → T)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) (j : Fin ω.1) :
    σ (finitePastRank (observedFiniteHistory ω (ω.2 j).1) (ω.2 j).1)=
      σ (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val := by
  rw [finitePastRank_observedHistory ω hClock j le_rfl]

end ProphetSecretary.Limiting
