import ProphetSecretary.Limiting.CountableFirstAcceptance

/-!
# Positive time changes of a countable first acceptance

Multiplying accepted clocks by a positive horizon preserves earliest codes,
including the equal-time label convention. The physical terminal time is the
horizon itself, so physical stopping duration scales by that horizon.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.FirstAcceptance
variable {Ω Ξ : Type*}

lemma earliest_timeScale_iff {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    {B : Ξ → ℕ → Prop} {v : Ξ → ℕ → ℝ} {ξ : Ξ} {h : ℝ} (hh : 0 < h)
    (hA : ∀ i, B ξ i ↔ A ω i) (hTime : ∀ i, A ω i → v ξ i=h*u ω i) (i : ℕ) :
    Earliest B v ξ i ↔ Earliest A u ω i := by
  constructor
  · intro hi
    have hai := (hA i).mp hi.1
    refine ⟨hai,?_⟩
    intro j hj
    have hOrder := hi.2 j ((hA j).mpr hj)
    have hLe : u ω i ≤ u ω j := by
      have h' := hOrder.1
      rw [hTime i hai,hTime j hj] at h'
      exact (mul_le_mul_iff_right₀ hh).mp h'
    refine ⟨hLe,?_⟩
    intro hEq
    apply hOrder.2
    rw [hTime i hai,hTime j hj,hEq]
  · intro hi
    refine ⟨(hA i).mpr hi.1,?_⟩
    intro j hj
    have haj := (hA j).mp hj
    have hOrder := hi.2 j haj
    refine ⟨?_,?_⟩
    · rw [hTime i hi.1,hTime j haj]
      exact mul_le_mul_of_nonneg_left hOrder.1 hh.le
    · intro hEq
      rw [hTime i hi.1,hTime j haj] at hEq
      exact hOrder.2 ((mul_right_inj' hh.ne').mp hEq)

lemma selectedCode_timeScale {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    {B : Ξ → ℕ → Prop} {v : Ξ → ℕ → ℝ} {ξ : Ξ} {h : ℝ} (hh : 0 < h)
    (hA : ∀ i, B ξ i ↔ A ω i) (hTime : ∀ i, A ω i → v ξ i=h*u ω i) :
    selectedCode B v ξ=selectedCode A u ω := by
  by_cases hFirst : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := hFirst
    have hPhys := (earliest_timeScale_iff hh hA hTime i).mpr hi
    rw [(selectedCode_eq_succ_iff _ _ _ _).mpr hPhys,(selectedCode_eq_succ_iff _ _ _ _).mpr hi]
  · have hNo : ¬∃ i, Earliest B v ξ i := by
      rintro ⟨i,hi⟩
      exact hFirst ⟨i,(earliest_timeScale_iff hh hA hTime i).mp hi⟩
    rw [(selectedCode_eq_zero_iff _ _ _).mpr hNo,(selectedCode_eq_zero_iff _ _ _).mpr hFirst]

noncomputable def stoppingTimeAt (h : ℝ) (A : Ω → ℕ → Prop) (u : Ω → ℕ → ℝ) : Ω → ℝ :=
  reward h A u u

lemma stoppingTimeAt_of_earliest (h : ℝ) {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω} {i : ℕ}
    (hi : Earliest A u ω i) : stoppingTimeAt h A u ω=u ω i := reward_of_earliest h hi

lemma stoppingTimeAt_of_no_first (h : ℝ) {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    (hNo : ¬∃ i, Earliest A u ω i) : stoppingTimeAt h A u ω=h := by
  rw [stoppingTimeAt,reward,(selectedCode_eq_zero_iff _ _ _).mpr hNo,if_pos rfl]

lemma stoppingTimeAt_timeScale {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    {B : Ξ → ℕ → Prop} {v : Ξ → ℕ → ℝ} {ξ : Ξ} {h : ℝ} (hh : 0 < h)
    (hA : ∀ i, B ξ i ↔ A ω i) (hTime : ∀ i, A ω i → v ξ i=h*u ω i) :
    stoppingTimeAt h B v ξ=h*stoppingTime A u ω := by
  by_cases hFirst : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := hFirst
    rw [stoppingTimeAt_of_earliest h ((earliest_timeScale_iff hh hA hTime i).mpr hi),
      stoppingTime_of_earliest hi,hTime i hi.1]
  · have hNo : ¬∃ i, Earliest B v ξ i := by
      rintro ⟨i,hi⟩
      exact hFirst ⟨i,(earliest_timeScale_iff hh hA hTime i).mp hi⟩
    rw [stoppingTimeAt_of_no_first h hNo,stoppingTime_of_no_first hFirst,mul_one]

lemma measurable_stoppingTimeAt [MeasurableSpace Ω] (h : ℝ) {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ}
    (hA : ∀ i, MeasurableSet {ω | A ω i}) (hu : ∀ i, Measurable (fun ω => u ω i)) :
    Measurable (stoppingTimeAt h A u) := measurable_reward h hA hu hu

lemma hasFirstIfAccepted_timeScale_iff {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ} {ω : Ω}
    {B : Ξ → ℕ → Prop} {v : Ξ → ℕ → ℝ} {ξ : Ξ} {h : ℝ} (hh : 0 < h)
    (hA : ∀ i, B ξ i ↔ A ω i) (hTime : ∀ i, A ω i → v ξ i=h*u ω i) :
    HasFirstIfAccepted B v ξ ↔ HasFirstIfAccepted A u ω := by
  constructor
  · intro hFirst ⟨i,hi⟩
    obtain ⟨j,hj⟩ := hFirst ⟨i,(hA i).mpr hi⟩
    exact ⟨j,(earliest_timeScale_iff hh hA hTime j).mp hj⟩
  · intro hFirst ⟨i,hi⟩
    obtain ⟨j,hj⟩ := hFirst ⟨i,(hA i).mp hi⟩
    exact ⟨j,(earliest_timeScale_iff hh hA hTime j).mpr hj⟩

lemma reward_timeScale (a : ℝ) {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω}
    {B : Ξ → ℕ → Prop} {v y : Ξ → ℕ → ℝ} {ξ : Ξ} {h : ℝ} (hh : 0 < h)
    (hA : ∀ i, B ξ i ↔ A ω i) (hTime : ∀ i, A ω i → v ξ i=h*u ω i)
    (hValue : ∀ i, A ω i → y ξ i=x ω i) : reward a B v y ξ=reward a A u x ω := by
  by_cases hFirst : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := hFirst
    rw [reward_of_earliest a ((earliest_timeScale_iff hh hA hTime i).mpr hi),reward_of_earliest a hi,hValue i hi.1]
  · have hNo : ¬∃ i, Earliest B v ξ i := by
      rintro ⟨i,hi⟩
      exact hFirst ⟨i,(earliest_timeScale_iff hh hA hTime i).mp hi⟩
    rw [reward,(selectedCode_eq_zero_iff _ _ _).mpr hNo,if_pos rfl,
      reward,(selectedCode_eq_zero_iff _ _ _).mpr hFirst,if_pos rfl]

lemma measurableSet_hasFirstIfAccepted [MeasurableSpace Ω] {A : Ω → ℕ → Prop} {u : Ω → ℕ → ℝ}
    (hA : ∀ i, MeasurableSet {ω | A ω i}) (hu : ∀ i, Measurable (fun ω => u ω i)) :
    MeasurableSet {ω | HasFirstIfAccepted A u ω} := by
  have hAx : MeasurableSet {ω | ∃ i, A ω i} := by
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion hA
  have hFirst : MeasurableSet {ω | ∃ i, Earliest A u ω i} := by
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion (measurableSet_earliest hA hu)
  have hEq : {ω | HasFirstIfAccepted A u ω} = {ω | ∃ i, A ω i}ᶜ ∪ {ω | ∃ i, Earliest A u ω i} := by
    ext ω
    simp only [HasFirstIfAccepted,mem_setOf_eq,mem_union,mem_compl_iff,imp_iff_not_or]
  rw [hEq]
  exact hAx.compl.union hFirst

end ProphetSecretary.Limiting.FirstAcceptance
