import Mathlib.MeasureTheory.MeasurableSpace.CountablyGenerated
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

/-!
# Countably many tests determine a finite measure

Finite intersections of the library's countable generating sequence form a
countable generating pi-system and include the whole space. This supplies
countable observable coordinates for locally finite point-measure bands.
-/

open MeasureTheory MeasurableSpace Set
open scoped Classical

namespace ProphetSecretary.Probability

variable (α : Type*) [MeasurableSpace α] [MeasurableSpace.CountablyGenerated α]

noncomputable def measureTest (s : Finset ℕ) : Set α :=
  ⋂ i ∈ s, MeasurableSpace.natGeneratingSequence α i

lemma measurableSet_measureTest (s : Finset ℕ) : MeasurableSet (measureTest α s) :=
  MeasurableSet.iInter (fun i => MeasurableSet.iInter (fun _ => MeasurableSpace.measurableSet_natGeneratingSequence i))

lemma measureTest_empty : measureTest α ∅ = univ := by simp [measureTest]

lemma measureTest_singleton (i : ℕ) : measureTest α {i} = MeasurableSpace.natGeneratingSequence α i := by
  simp [measureTest]

lemma measureTest_union (s t : Finset ℕ) : measureTest α (s ∪ t) = measureTest α s ∩ measureTest α t := by
  ext x
  simp only [measureTest,mem_iInter,Finset.mem_union,or_imp,forall_and,mem_inter_iff]

lemma isPiSystem_measureTests : IsPiSystem (Set.range (measureTest α)) := by
  rintro _ ⟨s,rfl⟩ _ ⟨t,rfl⟩ _
  exact ⟨s ∪ t,measureTest_union α s t⟩

lemma generateFrom_measureTests : MeasurableSpace.generateFrom (Set.range (measureTest α)) =
    (inferInstance : MeasurableSpace α) := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro _ ⟨s,rfl⟩
    exact measurableSet_measureTest α s
  · refine (le_of_eq (MeasurableSpace.generateFrom_natGeneratingSequence α).symm).trans ?_
    apply MeasurableSpace.generateFrom_mono
    rintro _ ⟨i,rfl⟩
    exact ⟨{i},measureTest_singleton α i⟩

lemma finiteMeasure_eq_of_tests (μ ν : Measure α) [IsFiniteMeasure μ]
    (h : ∀ s : Finset ℕ, μ (measureTest α s) = ν (measureTest α s)) : μ = ν := by
  apply MeasureTheory.ext_of_generate_finite (Set.range (measureTest α))
    (generateFrom_measureTests α).symm (isPiSystem_measureTests α)
  · rintro _ ⟨s,rfl⟩
    exact h s
  · simpa only [measureTest_empty] using h ∅

end ProphetSecretary.Probability
