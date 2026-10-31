import ProphetSecretary.Model.Instance
import ProphetSecretary.Model.Measurability

/-!
# Selected rewards and duration

The selected reward is zero when there is no acceptance. At distinct arrival times there
is at most one selected identity, so this reward is precisely that offer's value. All
bounds are proved on complete executions; no future observation is supplied to a policy.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {Seed : Type*} {n : ℕ}

/-- The smallest identity among simultaneous earliest acceptances. This deterministic
rule makes selection unique even on clock ties, which have probability zero in the model. -/
def Policy.ActualSelects (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (i : Fin n) : Prop :=
  π.Selects r D x u i ∧ ∀ j, π.Selects r D x u j → i ≤ j

theorem Policy.actualSelects_unique (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) {i j : Fin n}
    (hi : π.ActualSelects r D x u i) (hj : π.ActualSelects r D x u j) : i = j :=
  le_antisymm (hi.2 j hj.1) (hj.2 i hi.1)

theorem Policy.actualSelects_iff_selects (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : Function.Injective u) (i : Fin n) :
    π.ActualSelects r D x u i ↔ π.Selects r D x u i := by
  refine ⟨And.left, fun hi => ⟨hi, ?_⟩⟩
  intro j hj
  exact le_of_eq (π.selects_unique r D x u hu hi hj)

theorem Policy.exists_actualSelects (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (h : ∃ i, π.Selects r D x u i) :
    ∃ i, π.ActualSelects r D x u i := by
  let A := Finset.univ.filter fun i => π.Selects r D x u i
  have hA : A.Nonempty := by
    obtain ⟨i, hi⟩ := h
    exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩⟩
  refine ⟨A.min' hA, ?_, ?_⟩
  · exact (Finset.mem_filter.mp (Finset.min'_mem A hA)).2
  · intro j hj
    exact Finset.min'_le A j (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩)

/-- The unique selected offer's value, with zero reward on no selection. -/
noncomputable def Policy.reward (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if π.ActualSelects r D x u i then x i else 0

theorem Policy.stoppingTime_eq_one_or_selects (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.stoppingTime r D x u = 1 ∨ ∃ i, π.Selects r D x u i := by
  have h := Finset.min'_mem (π.stopTimes r D x u) ⟨1, Finset.mem_insert_self _ _⟩
  rcases Finset.mem_insert.mp h with h | h
  · exact Or.inl h
  · obtain ⟨i, hi, he⟩ := Finset.mem_image.mp h
    exact Or.inr ⟨i, hi, he⟩

theorem Policy.stoppingTime_eq_one_or_actualSelects (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.stoppingTime r D x u = 1 ∨ ∃ i, π.ActualSelects r D x u i := by
  rcases π.stoppingTime_eq_one_or_selects r D x u with ht | h
  · exact Or.inl ht
  · exact Or.inr (π.exists_actualSelects r D x u h)

theorem Policy.reward_eq_of_actualSelects (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ)
    {i : Fin n} (hi : π.ActualSelects r D x u i) : π.reward r D x u = x i := by
  unfold Policy.reward
  rw [Finset.sum_eq_single i]
  · simp [hi]
  · intro j _ hji
    have hj : ¬π.ActualSelects r D x u j := fun hj => hji (π.actualSelects_unique r D x u hj hi)
    simp [hj]
  · simp

theorem Policy.reward_eq_of_selects (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : Function.Injective u)
    {i : Fin n} (hi : π.Selects r D x u i) : π.reward r D x u = x i :=
  π.reward_eq_of_actualSelects r D x u ((π.actualSelects_iff_selects r D x u hu i).mpr hi)

theorem Policy.reward_eq_zero_of_no_actualSelection (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (h : ∀ i, ¬π.ActualSelects r D x u i) :
    π.reward r D x u = 0 := by
  simp [Policy.reward, h]

theorem Policy.reward_eq_zero_of_no_selection (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (h : ∀ i, ¬π.Selects r D x u i) :
    π.reward r D x u = 0 := by
  exact π.reward_eq_zero_of_no_actualSelection r D x u (fun i hi => h i hi.1)

theorem Policy.stoppingTime_eq_one_of_no_selection (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (h : ∀ i, ¬π.Selects r D x u i) :
    π.stoppingTime r D x u = 1 := by
  rcases π.stoppingTime_eq_one_or_selects r D x u with ht | ⟨i, hi⟩
  · exact ht
  · exact False.elim (h i hi)

theorem Policy.stoppingTime_eq_one_of_no_actualSelection (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (h : ∀ i, ¬π.ActualSelects r D x u i) :
    π.stoppingTime r D x u = 1 := by
  rcases π.stoppingTime_eq_one_or_actualSelects r D x u with ht | ⟨i, hi⟩
  · exact ht
  · exact False.elim (h i hi)

theorem Policy.reward_nonnegative (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) :
    0 ≤ π.reward r D x u := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hx i
  · exact le_rfl

theorem Policy.reward_le_maximum (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.reward r D x u ≤ Instance.maximum x := by
  by_cases h : ∃ i, π.ActualSelects r D x u i
  · obtain ⟨i, hi⟩ := h
    rw [π.reward_eq_of_actualSelects r D x u hi]
    exact Instance.le_maximum x i
  · rw [π.reward_eq_zero_of_no_actualSelection r D x u (fun i hi => h ⟨i, hi⟩)]
    exact Instance.maximum_nonnegative x

theorem Policy.selects_implies_reaches (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) {i : Fin n} (hi : π.Selects r Finset.univ x u i) :
    π.Reaches r x u i := le_of_eq hi.2

/-- Finitely many strictly positive clocks force strictly positive duration, including
for the empty instance, whose duration is one. -/
theorem Policy.stoppingTime_positive (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : ∀ i, 0 < u i) :
    0 < π.stoppingTime r D x u := by
  rcases π.stoppingTime_eq_one_or_selects r D x u with ht | ⟨i, hi⟩
  · rw [ht]
    exact zero_lt_one
  · rw [← hi.2]
    exact hu i

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]

theorem Policy.measurableSet_actualSelects (π : Policy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j)
    (D : Finset (Fin n)) (i : Fin n) :
    MeasurableSet {ω | π.ActualSelects (r ω) D (x ω) (u ω) i} := by
  apply (π.measurableSet_selects hπ hr hx hu D i).inter
  change MeasurableSet {ω | ∀ j, π.Selects (r ω) D (x ω) (u ω) j → i ≤ j}
  rw [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro j
  by_cases hij : i ≤ j
  · simp [hij]
  · simpa only [hij, imp_false, Set.compl_setOf] using
      (π.measurableSet_selects hπ hr hx hu D j).compl

theorem Policy.measurable_reward (π : Policy Seed n) (hπ : π.IsMeasurable)
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ j, Measurable fun ω => x ω j) (hu : ∀ j, Measurable fun ω => u ω j)
    (D : Finset (Fin n)) :
    Measurable fun ω => π.reward (r ω) D (x ω) (u ω) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (π.measurableSet_actualSelects hπ hr hx hu D i) (hx i) measurable_const

end ProphetSecretary.Model
