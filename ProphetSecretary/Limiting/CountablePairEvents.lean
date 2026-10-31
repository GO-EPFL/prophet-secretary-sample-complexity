import ProphetSecretary.Limiting.CountableCandidates

/-!
# Positive close-pair events on the full countable input

Finite-prefix events keep every anonymous point and successively include the
individual identities. Their increasing union is the full event; no policy's
stopping decision enters these analytical events.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def candidatePrefixLevel : Candidate → ℕ
  | Sum.inl i => i+1
  | Sum.inr _ => 0

def closePositivePair {Seed : Type*} (b η : ℝ) : Set (CompleteWorld Seed) :=
  {v | ∃ i j : Candidate, i ≠ j ∧ candidatePresent v i ∧ candidatePresent v j ∧
    b < (candidatePoint v i).2 ∧ b < (candidatePoint v j).2 ∧
      |(candidatePoint v i).1-(candidatePoint v j).1| ≤ η}

def prefixClosePositivePair {Seed : Type*} (N : ℕ) (b η : ℝ) : Set (CompleteWorld Seed) :=
  {v | ∃ i j : Candidate, (candidatePrefixLevel i ≤ N ∧ candidatePrefixLevel j ≤ N ∧ i ≠ j) ∧
    candidatePresent v i ∧ candidatePresent v j ∧ b < (candidatePoint v i).2 ∧
    b < (candidatePoint v j).2 ∧ |(candidatePoint v i).1-(candidatePoint v j).1| ≤ η}

lemma measurableSet_closePositivePair {Seed : Type*} [MeasurableSpace Seed] (b η : ℝ) :
    MeasurableSet (closePositivePair b η : Set (CompleteWorld Seed)) := by
  simp only [closePositivePair,setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  exact (MeasurableSet.const (i ≠ j)).inter ((measurableSet_candidatePresent i).inter
    ((measurableSet_candidatePresent j).inter
      ((measurableSet_lt measurable_const (measurable_candidatePoint i).snd).inter
        ((measurableSet_lt measurable_const (measurable_candidatePoint j).snd).inter
          (measurableSet_le (continuous_abs.measurable.comp
            ((measurable_candidatePoint i).fst.sub (measurable_candidatePoint j).fst)) measurable_const)))))

lemma measurableSet_prefixClosePositivePair {Seed : Type*} [MeasurableSpace Seed]
    (N : ℕ) (b η : ℝ) : MeasurableSet (prefixClosePositivePair N b η : Set (CompleteWorld Seed)) := by
  simp only [prefixClosePositivePair,setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  apply MeasurableSet.iUnion
  intro j
  exact (MeasurableSet.const (candidatePrefixLevel i ≤ N ∧ candidatePrefixLevel j ≤ N ∧ i ≠ j)).inter
    ((measurableSet_candidatePresent i).inter ((measurableSet_candidatePresent j).inter
      ((measurableSet_lt measurable_const (measurable_candidatePoint i).snd).inter
        ((measurableSet_lt measurable_const (measurable_candidatePoint j).snd).inter
          (measurableSet_le (continuous_abs.measurable.comp
            ((measurable_candidatePoint i).fst.sub (measurable_candidatePoint j).fst)) measurable_const)))))

lemma prefixClosePositivePair_mono {Seed : Type*} (b η : ℝ) :
    Monotone (fun N => (prefixClosePositivePair N b η : Set (CompleteWorld Seed))) := by
  intro N M hNM v hv
  obtain ⟨i,j,hIndex,hRest⟩ := hv
  exact ⟨i,j,⟨hIndex.1.trans hNM,hIndex.2.1.trans hNM,hIndex.2.2⟩,hRest⟩

lemma iUnion_prefixClosePositivePair {Seed : Type*} (b η : ℝ) :
    (⋃ N, prefixClosePositivePair N b η : Set (CompleteWorld Seed))=closePositivePair b η := by
  ext v
  constructor
  · intro hv
    obtain ⟨N,hN⟩ := mem_iUnion.mp hv
    obtain ⟨i,j,hIndex,hRest⟩ := hN
    exact ⟨i,j,hIndex.2.2,hRest⟩
  · rintro ⟨i,j,hij,hRest⟩
    apply mem_iUnion.mpr
    exact ⟨max (candidatePrefixLevel i) (candidatePrefixLevel j),i,j,
      ⟨le_max_left _ _,le_max_right _ _,hij⟩,hRest⟩

end ProphetSecretary.Limiting.CountableInstance
