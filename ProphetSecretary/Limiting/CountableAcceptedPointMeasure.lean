import ProphetSecretary.Limiting.CountableFirstAcceptance
import ProphetSecretary.Limiting.FirstPointReward

/-!
# Executed countable outcomes from their accepted-point measure

The measure is analytical: callbacks are still evaluated only on their past.
Attainment and distinct accepted clocks identify its first slice with exactly
one selected point and hence identify both observable payoff functionals.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting.FirstAcceptance

variable {Ω : Type*}

noncomputable def pointMeasure (A : Ω → ℕ → Prop) (u x : Ω → ℕ → ℝ) (ω : Ω) : Measure Point :=
  Measure.sum (fun i => if A ω i then Measure.dirac (u ω i,x ω i) else 0)

lemma pointMeasure_eq_zero {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω}
    (hA : ¬∃ i, A ω i) : pointMeasure A u x ω = 0 := by
  apply Measure.sum_eq_zero.mpr
  intro i
  exact if_neg (fun hi => hA ⟨i,hi⟩)

lemma pointMeasure_past_pos_iff (A : Ω → ℕ → Prop) (u x : Ω → ℕ → ℝ) (ω : Ω) (t : ℝ) :
    0 < pointMeasure A u x ω (Iio t ×ˢ univ) ↔ ∃ i, A ω i ∧ u ω i < t := by
  have hS : MeasurableSet (Iio t ×ˢ (univ : Set ℝ)) := measurableSet_Iio.prod MeasurableSet.univ
  constructor
  · intro hp
    by_contra hn
    have hz : pointMeasure A u x ω (Iio t ×ˢ univ) = 0 := by
      apply Measure.sum_apply_eq_zero.mpr
      intro i
      by_cases hi : A ω i
      · have ht : ¬u ω i < t := fun ht => hn ⟨i,hi,ht⟩
        simp [hi,Measure.dirac_apply' _ hS,ht]
      · simp [hi]
    exact hp.ne' hz
  · rintro ⟨i,hi,ht⟩
    have hle := Measure.le_iff.mp
      (Measure.le_sum (fun j => if A ω j then Measure.dirac (u ω j,x ω j) else 0) i)
      (Iio t ×ˢ univ) hS
    simp [hi,Measure.dirac_apply' _ hS,ht] at hle
    exact zero_lt_one.trans_le hle

lemma pointMeasure_firstSlice {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω} {i : ℕ}
    (hi : A ω i) (hinj : Set.InjOn (u ω) {j | A ω j}) :
    (pointMeasure A u x ω).restrict {p : Point | p.1 = u ω i} = Measure.dirac (u ω i,x ω i) := by
  have hS : MeasurableSet {p : Point | p.1 = u ω i} := measurableSet_eq_fun measurable_fst measurable_const
  rw [pointMeasure,Measure.restrict_sum _ hS]
  have he (j : ℕ) : (if A ω j then Measure.dirac (u ω j,x ω j) else 0).restrict {p : Point | p.1 = u ω i} =
      if j = i then Measure.dirac (u ω i,x ω i) else 0 := by
    by_cases hji : j = i
    · subst j
      simp only [if_pos hi,restrict_dirac' hS,mem_setOf_eq]
    · by_cases hj : A ω j
      · have ht : u ω j ≠ u ω i := fun ht => hji (hinj hj hi ht)
        simp only [if_pos hj,restrict_dirac' hS,mem_setOf_eq,if_neg ht,if_neg hji]
      · simp only [if_neg hj,Measure.restrict_zero,if_neg hji]
  simp_rw [he]
  ext S hS
  rw [Measure.sum_apply _ hS]
  have hterm (j : ℕ) : (if j = i then Measure.dirac (u ω i,x ω i) else 0) S =
      if j = i then (Measure.dirac (u ω i,x ω i)) S else 0 := by split_ifs <;> rfl
  simp_rw [hterm]
  simp

lemma pointMeasure_time_eq {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω}
    (hfirst : HasFirstIfAccepted A u ω) (hu : ∀ i, A ω i → u ω i ∈ Icc (0 : ℝ) 1) :
    FirstPoint.time (pointMeasure A u x ω) = stoppingTime A u ω := by
  by_cases he : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := he
    rw [stoppingTime_of_earliest hi]
    apply FirstPoint.time_eq_of_rational_cumulatives _ (hu i hi.1)
    · intro q hq
      obtain ⟨j,hj,ht⟩ := (pointMeasure_past_pos_iff A u x ω q).mp hq
      exact (hi.2 j hj).1.trans ht.le
    · intro q hq
      exact (pointMeasure_past_pos_iff A u x ω q).mpr ⟨i,hi.1,hq⟩
  · have hno := (no_first_iff_no_accepted hfirst).mp he
    rw [pointMeasure_eq_zero hno,stoppingTime_of_no_first he]
    apply FirstPoint.time_eq_one_of_empty_cumulatives
    intro q
    rfl

lemma pointMeasure_reward_eq (a : ℝ) (μ : FiniteMeasure Point)
    {A : Ω → ℕ → Prop} {u x : Ω → ℕ → ℝ} {ω : Ω}
    (hmeasure : (μ : Measure Point) = pointMeasure A u x ω)
    (hfirst : HasFirstIfAccepted A u ω) (hu : ∀ i, A ω i → u ω i ∈ Icc (0 : ℝ) 1)
    (hx : ∀ i, A ω i → 0 ≤ x ω i) (hinj : Set.InjOn (u ω) {i | A ω i}) :
    FirstPoint.reward a μ = reward a A u x ω := by
  by_cases he : ∃ i, Earliest A u ω i
  · obtain ⟨i,hi⟩ := he
    rw [reward_of_earliest a hi]
    have ht : FirstPoint.time (μ : Measure Point) = u ω i := by
      rw [hmeasure,pointMeasure_time_eq hfirst hu,stoppingTime_of_earliest hi]
    have hnonzero : (μ : Measure Point) univ ≠ 0 := by
      have hle := Measure.le_iff.mp
        (Measure.le_sum (fun j => if A ω j then Measure.dirac (u ω j,x ω j) else 0) i)
        univ MeasurableSet.univ
      simp only [if_pos hi.1,measure_univ] at hle
      rw [hmeasure]
      exact ne_of_gt (zero_lt_one.trans_le hle)
    apply FirstPoint.reward_of_firstSlice a μ (hx i hi.1) hnonzero
    rw [ht,hmeasure]
    exact pointMeasure_firstSlice hi.1 hinj
  · have hno := (no_first_iff_no_accepted hfirst).mp he
    rw [reward,(selectedCode_eq_zero_iff _ _ _).mpr he,if_pos rfl]
    apply FirstPoint.reward_of_empty
    rw [hmeasure,pointMeasure_eq_zero hno]
    rfl

end ProphetSecretary.Limiting.FirstAcceptance
