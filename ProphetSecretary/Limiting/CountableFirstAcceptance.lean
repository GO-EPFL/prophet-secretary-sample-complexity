import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.Data.Set.Finite.Lemmas

/-!
# Measurable first acceptance in a countable candidate set

A least accepted time must actually be attained. A decreasing sequence of
accepted times with no first point does not define a stopping policy. This
construction gives measurable reward and duration and proves attainment when
the accepted set is finite. It imposes no finite-support assumption on offers.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.FirstAcceptance

variable {Ω : Type*}

/-- Natural labels only break ties at an equal physical time. -/
def Earliest (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) (i : ℕ) : Prop :=
  A ω i ∧ ∀ j, A ω j → u ω i ≤ u ω j ∧ (u ω i = u ω j → i ≤ j)

lemma earliest_unique {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω} {i j : ℕ}
    (hi : Earliest A u ω i) (hj : Earliest A u ω j) : i = j := by
  have ht : u ω i = u ω j := le_antisymm (hi.2 j hj.1).1 (hj.2 i hi.1).1
  exact le_antisymm ((hi.2 j hj.1).2 ht) ((hj.2 i hi.1).2 ht.symm)

lemma exists_earliest_of_finite {A : Ω → ℕ → Prop} (u : Ω → ℕ → ℝ) (ω : Ω)
    (hfinite : {i | A ω i}.Finite) (hne : ∃ i, A ω i) : ∃ i, Earliest A u ω i := by
  obtain ⟨i,hi,hmin⟩ := Set.exists_min_image {i | A ω i} (u ω) hfinite hne
  have hex : ∃ j, A ω j ∧ u ω j = u ω i := ⟨i,hi,rfl⟩
  refine ⟨Nat.find hex,(Nat.find_spec hex).1,?_⟩
  intro j hj
  have he := (Nat.find_spec hex).2
  refine ⟨he.trans_le (hmin j hj),?_⟩
  intro hij
  exact Nat.find_min' hex ⟨hj,hij.symm.trans he⟩

noncomputable def indexPredicate (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) : ℕ → Prop
  | 0 => ¬∃ i, Earliest A u ω i
  | i+1 => Earliest A u ω i

lemma exists_indexPredicate (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) :
    ∃ k, indexPredicate A u ω k := by
  by_cases h : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := h
    exact ⟨i+1,hi⟩
  · exact ⟨0,h⟩

/-- Zero means no first point; i+1 means that candidate i is first. -/
noncomputable def selectedCode (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) : ℕ :=
  Nat.find (exists_indexPredicate A u ω)

lemma selectedCode_eq_zero_iff (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) :
    selectedCode A u ω = 0 ↔ ¬∃ i, Earliest A u ω i :=
  Nat.find_eq_zero _

lemma selectedCode_eq_succ_iff (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) (i : ℕ) :
    selectedCode A u ω = i+1 ↔ Earliest A u ω i := by
  constructor
  · intro he
    have hs := Nat.find_spec (exists_indexPredicate A u ω)
    rw [← selectedCode,he] at hs
    exact hs
  · intro hi
    have hs := Nat.find_spec (exists_indexPredicate A u ω)
    change indexPredicate A u ω (selectedCode A u ω) at hs
    cases hc : selectedCode A u ω with
    | zero =>
      rw [hc] at hs
      exact False.elim (hs ⟨i,hi⟩)
    | succ j =>
      rw [hc] at hs
      have he := earliest_unique hs hi
      exact congrArg Nat.succ he

noncomputable def reward (a : ℝ) (A : Ω → ℕ → Prop) (u x : Ω → ℕ → ℝ) (ω : Ω) : ℝ :=
  if selectedCode A u ω = 0 then a else x ω (selectedCode A u ω - 1)

noncomputable def stoppingTime (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) : ℝ :=
  if selectedCode A u ω = 0 then 1 else u ω (selectedCode A u ω - 1)

lemma reward_of_earliest (a : ℝ) {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω} {i : ℕ}
    (hi : Earliest A u ω i) : reward a A u x ω = x ω i := by
  rw [reward,(selectedCode_eq_succ_iff _ _ _ _).mpr hi]
  simp

lemma stoppingTime_of_earliest {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω} {i : ℕ}
    (hi : Earliest A u ω i) : stoppingTime A u ω = u ω i := by
  rw [stoppingTime,(selectedCode_eq_succ_iff _ _ _ _).mpr hi]
  simp

lemma stoppingTime_of_no_first {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    (h : ¬∃ i, Earliest A u ω i) : stoppingTime A u ω = 1 := by
  rw [stoppingTime,(selectedCode_eq_zero_iff _ _ _).mpr h,if_pos rfl]

/-- Attainment is the execution requirement. Infinite accepted sets are allowed
when they possess a first point; finiteness is only a sufficient condition. -/
def HasFirstIfAccepted (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω) : Prop :=
  (∃ i, A ω i) → ∃ i, Earliest A u ω i

lemma hasFirstIfAccepted_of_finite (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω)
    (hfinite : {i | A ω i}.Finite) : HasFirstIfAccepted A u ω :=
  exists_earliest_of_finite u ω hfinite

lemma no_first_iff_no_accepted {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    (hfirst : HasFirstIfAccepted A u ω) :
    (¬∃ i, Earliest A u ω i) ↔ ¬∃ i, A ω i := by
  constructor
  · exact fun h hA => h (hfirst hA)
  · rintro h ⟨i,hi⟩
    exact h ⟨i,hi.1⟩

lemma stoppingTime_le_one {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    (hu : ∀ i, A ω i → u ω i ≤ 1) : stoppingTime A u ω ≤ 1 := by
  by_cases he : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := he
    rw [stoppingTime_of_earliest hi]
    exact hu i hi.1
  · rw [stoppingTime_of_no_first he]

lemma le_stoppingTime_iff {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    (hfirst : HasFirstIfAccepted A u ω) (hu : ∀ i, A ω i → u ω i ≤ 1) (t : ℝ) :
    t ≤ stoppingTime A u ω ↔ t ≤ 1 ∧ ∀ i, A ω i → t ≤ u ω i := by
  constructor
  · intro ht
    refine ⟨ht.trans (stoppingTime_le_one hu),?_⟩
    intro i hi
    obtain ⟨j,hj⟩ := hfirst ⟨i,hi⟩
    rw [stoppingTime_of_earliest hj] at ht
    exact ht.trans (hj.2 i hi).1
  · rintro ⟨ht,h⟩
    by_cases he : ∃ i, Earliest A u ω i
    · obtain ⟨i,hi⟩ := he
      rw [stoppingTime_of_earliest hi]
      exact h i hi.1
    · rw [stoppingTime_of_no_first he]
      exact ht

lemma reward_bounded {a H : ℝ} (ha : a ∈ Icc (0 : ℝ) H)
    {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω}
    (hx : ∀ i, A ω i → x ω i ∈ Icc (0 : ℝ) H) : reward a A u x ω ∈ Icc (0 : ℝ) H := by
  by_cases he : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := he
    rw [reward_of_earliest a hi]
    exact hx i hi.1
  · rw [reward,(selectedCode_eq_zero_iff _ _ _).mpr he,if_pos rfl]
    exact ha

/-- Local finiteness before every time strictly below one is enough: an
infinite set accumulating only at the terminal time is allowed. -/
lemma hasFirstIfAccepted_of_locallyFinite (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) (ω : Ω)
    (hupper : ∀ i, A ω i → u ω i ≤ 1)
    (hlocal : ∀ t < (1 : ℝ), {i | A ω i ∧ u ω i ≤ t}.Finite) :
    HasFirstIfAccepted A u ω := by
  intro hne
  by_cases hbefore : ∃ i, A ω i ∧ u ω i < 1
  · obtain ⟨i,hi,hti⟩ := hbefore
    let D : Ω → ℕ → Prop := fun _ j => A ω j ∧ u ω j ≤ u ω i
    obtain ⟨j,hj⟩ := exists_earliest_of_finite (A := D) u ω (hlocal (u ω i) hti) ⟨i,hi,le_rfl⟩
    refine ⟨j,hj.1.1,?_⟩
    intro k hk
    by_cases hki : u ω k ≤ u ω i
    · exact hj.2 k ⟨hk,hki⟩
    · have hstrict : u ω j < u ω k := hj.1.2.trans_lt (lt_of_not_ge hki)
      exact ⟨hstrict.le,fun he => False.elim ((ne_of_lt hstrict) he)⟩
  · have htime (i : ℕ) (hi : A ω i) : u ω i = 1 := by
      apply le_antisymm (hupper i hi)
      by_contra hn
      exact hbefore ⟨i,hi,lt_of_not_ge hn⟩
    refine ⟨Nat.find hne,Nat.find_spec hne,?_⟩
    intro j hj
    exact ⟨by rw [htime _ (Nat.find_spec hne),htime j hj],fun _ => Nat.find_min' hne hj⟩

variable [MeasurableSpace Ω]

lemma measurableSet_earliest {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ}
    (hA : ∀ i, MeasurableSet {ω | A ω i}) (hu : ∀ i, Measurable (fun ω => u ω i)) (i : ℕ) :
    MeasurableSet {ω | Earliest A u ω i} := by
  unfold Earliest
  simp only [setOf_and,setOf_forall]
  apply (hA i).inter
  apply MeasurableSet.iInter
  intro j
  simp only [imp_iff_not_or,setOf_or,← compl_setOf]
  apply (hA j).compl.union
  apply (measurableSet_le (hu i) (hu j)).inter
  by_cases hij : i ≤ j
  · simp only [hij,or_true]
    exact MeasurableSet.univ
  · simp only [hij,or_false]
    exact (measurableSet_eq_fun (hu i) (hu j)).compl

lemma measurableSet_indexPredicate {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ}
    (hA : ∀ i, MeasurableSet {ω | A ω i}) (hu : ∀ i, Measurable (fun ω => u ω i)) (k : ℕ) :
    MeasurableSet {ω | indexPredicate A u ω k} := by
  cases k with
  | zero =>
    change MeasurableSet {ω | ¬∃ i, Earliest A u ω i}
    have he : {ω | ¬∃ i, Earliest A u ω i} =
        (⋃ i, {ω | Earliest A u ω i})ᶜ := by ext ω; simp
    rw [he]
    exact (MeasurableSet.iUnion (fun i => measurableSet_earliest hA hu i)).compl
  | succ i => exact measurableSet_earliest hA hu i

lemma measurable_selectedCode {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ}
    (hA : ∀ i, MeasurableSet {ω | A ω i}) (hu : ∀ i, Measurable (fun ω => u ω i)) :
    Measurable (selectedCode A u) :=
  measurable_find (exists_indexPredicate A u) (measurableSet_indexPredicate hA hu)

lemma measurable_reward (a : ℝ) {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ}
    (hA : ∀ i, MeasurableSet {ω | A ω i}) (hu : ∀ i, Measurable (fun ω => u ω i))
    (hx : ∀ i, Measurable (fun ω => x ω i)) : Measurable (reward a A u x) := by
  let f : ℕ → Ω → ℝ := fun k ω => if k = 0 then a else x ω (k-1)
  have hf (k : ℕ) : Measurable (f k) := by
    dsimp only [f]
    by_cases hk : k = 0
    · simp only [hk]
      exact measurable_const
    · simp only [if_neg hk]
      exact hx (k-1)
  change Measurable (fun ω => f (Nat.find (exists_indexPredicate A u ω)) ω)
  exact Measurable.find hf (measurableSet_indexPredicate hA hu) (exists_indexPredicate A u)

lemma measurable_stoppingTime {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ}
    (hA : ∀ i, MeasurableSet {ω | A ω i}) (hu : ∀ i, Measurable (fun ω => u ω i)) :
    Measurable (stoppingTime A u) := by
  exact measurable_reward 1 hA hu hu

end ProphetSecretary.Limiting.FirstAcceptance
