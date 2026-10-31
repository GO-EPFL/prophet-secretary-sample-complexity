import ProphetSecretary.Limiting.CountableFirstAcceptance

/-!
# Analytical infimum of accepted arrival times

This measurable functional is defined even if an exceptional configuration has
accepted times without a first point. It agrees with the executed duration
whenever a first acceptance is attained. This distinction permits a pending
candidate to be placed at terminal time without assuming admissibility on a
null clock slice.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.FirstAcceptance
variable {Ω : Type*}

noncomputable def infimumTime (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) : ℝ :=
  ⨅ i : ℕ, if A ω i then u ω i else 1

lemma infimumTime_bounds {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    (hu : ∀ i, A ω i → u ω i ∈ Icc (0 : ℝ) 1) : infimumTime A u ω ∈ Icc (0 : ℝ) 1 := by
  have hTerm (i : ℕ) : (if A ω i then u ω i else 1) ∈ Icc (0 : ℝ) 1 := by
    split_ifs with h
    · exact hu i h
    · exact ⟨zero_le_one,le_rfl⟩
  have hBelow : BddBelow (range (fun i : ℕ => if A ω i then u ω i else 1)) :=
    ⟨0,fun _ ⟨i,hi⟩ => hi ▸ (hTerm i).1⟩
  exact ⟨le_ciInf (fun i => (hTerm i).1),(ciInf_le hBelow 0).trans (hTerm 0).2⟩

lemma le_infimumTime_iff {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    (hu : ∀ i, A ω i → u ω i ∈ Icc (0 : ℝ) 1) (t : ℝ) :
    t ≤ infimumTime A u ω ↔ t ≤ 1 ∧ ∀ i, A ω i → t ≤ u ω i := by
  have hBelow : BddBelow (range (fun i : ℕ => if A ω i then u ω i else 1)) := by
    refine ⟨0,?_⟩
    rintro _ ⟨i,rfl⟩
    dsimp only
    split_ifs with hi
    · exact (hu i hi).1
    · exact zero_le_one
  constructor
  · intro ht
    refine ⟨ht.trans (infimumTime_bounds hu).2,?_⟩
    intro i hi
    have h := ht.trans (ciInf_le hBelow i)
    simpa only [if_pos hi] using h
  · rintro ⟨ht,h⟩
    apply le_ciInf
    intro i
    split_ifs with hi
    · exact h i hi
    · exact ht

lemma infimumTime_of_earliest {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω} {i : ℕ}
    (hu : ∀ j, A ω j → u ω j ∈ Icc (0 : ℝ) 1) (hi : Earliest A u ω i) :
    infimumTime A u ω=u ω i := by
  apply le_antisymm
  · have h := (le_infimumTime_iff hu (infimumTime A u ω)).mp le_rfl
    exact h.2 i hi.1
  · apply (le_infimumTime_iff hu _).mpr
    exact ⟨(hu i hi.1).2,fun j hj => (hi.2 j hj).1⟩

lemma infimumTime_of_no_accepted {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    (h : ¬∃ i, A ω i) : infimumTime A u ω=1 := by
  have hN (i : ℕ) : ¬A ω i := fun hi => h ⟨i,hi⟩
  simp only [infimumTime,if_neg (hN _),ciInf_const]

lemma infimumTime_eq_stoppingTime {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    (hu : ∀ i, A ω i → u ω i ∈ Icc (0 : ℝ) 1)
    (hFirst : HasFirstIfAccepted A u ω) : infimumTime A u ω=stoppingTime A u ω := by
  by_cases h : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := h
    rw [infimumTime_of_earliest hu hi,stoppingTime_of_earliest hi]
  · rw [stoppingTime_of_no_first h,infimumTime_of_no_accepted ((no_first_iff_no_accepted hFirst).mp h)]

lemma measurable_infimumTime [MeasurableSpace Ω] {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ}
    (hA : ∀ i, MeasurableSet {ω | A ω i}) (hu : ∀ i, Measurable (fun ω => u ω i)) :
    Measurable (infimumTime A u) := by
  apply Measurable.iInf
  intro i
  exact Measurable.ite (hA i) (hu i) measurable_const

end ProphetSecretary.Limiting.FirstAcceptance
