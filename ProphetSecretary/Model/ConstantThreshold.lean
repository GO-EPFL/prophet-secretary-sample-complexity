import ProphetSecretary.Model.CompetitiveBasic
import ProphetSecretary.Reach.FiniteStrictReach
import ProphetSecretary.Probability.JackpotCoupling

/-!
# Constant thresholds and the half-prophet guarantee

A constant threshold accepts the first qualifying offer. Its reach event remains
independent of the current offer's value, even though every earlier identity is observed.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {Seed : Type*} {n : ℕ}

lemma Policy.exists_actualSelects_of_accepted (π : Policy Seed n) (r : Seed)
    (D : Finset (Fin n)) (x u : Fin n → ℝ) (hu : ∀ j, u j ≤ 1)
    (hA : (π.accepted r D x u).Nonempty) : ∃ i, π.ActualSelects r D x u i := by
  obtain ⟨i, hi, hmin⟩ := Finset.exists_min_image (π.accepted r D x u) u hA
  have ht : π.stoppingTime r D x u = u i := by
    apply le_antisymm (π.stoppingTime_le_of_accepted _ _ _ _ _ hi)
    exact (π.le_stoppingTime_iff r D x u (u i)).mpr ⟨hu i, hmin⟩
  exact π.exists_actualSelects r D x u ⟨i, hi, ht.symm⟩

noncomputable def constantThresholdRule (t : ℝ) (n : ℕ) : Policy Unit n :=
  thresholdPolicy (fun _ _ _ _ => t)

@[simp] lemma constantThresholdRule_action (t : ℝ) (x u : Fin n → ℝ)
    (D : Finset (Fin n)) (i : Fin n) :
    (constantThresholdRule t n).action () D x u i = true ↔ t ≤ x i := by
  simp [constantThresholdRule, Policy.action, thresholdPolicy]

lemma constantThresholdRule_isMeasurable (t : ℝ) (n : ℕ) :
    (constantThresholdRule t n).IsMeasurable := by
  let T := Unit × (ℝ × (Fin n × (ℝ × History n)))
  have hx : Measurable (fun z : T => z.2.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp (measurable_snd.comp measurable_snd))
  have hm : Measurable (fun z : T => if t ≤ z.2.2.2.1 then true else false) :=
    Measurable.ite (measurableSet_le measurable_const hx) measurable_const measurable_const
  change Measurable (fun z : T => decide (t ≤ z.2.2.2.1))
  convert hm using 1
  funext z
  split_ifs <;> simp_all

noncomputable def RandomizedPolicy.constantThreshold (t : ℝ) (n : ℕ) : RandomizedPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := constantThresholdRule t n
  measurable_rule := constantThresholdRule_isMeasurable t n

lemma constantThresholdRule_actualSelects_iff (t : ℝ) (x u : Fin n → ℝ)
    (hu : Function.Injective u) (i : Fin n) :
    (constantThresholdRule t n).ActualSelects () Finset.univ x u i ↔
      t ≤ x i ∧ (constantThresholdRule t n).Reaches () x u i := by
  let π := constantThresholdRule t n
  rw [π.actualSelects_iff_selects _ _ _ _ hu]
  constructor
  · intro h
    exact ⟨(constantThresholdRule_action t x u Finset.univ i).mp (π.mem_accepted _ _ _ _ i |>.mp h.1).2,
      π.selects_implies_reaches _ _ _ h⟩
  · rintro ⟨hx, hr⟩
    have ha : i ∈ π.accepted () Finset.univ x u :=
      (π.mem_accepted _ _ _ _ i).mpr ⟨Finset.mem_univ _, (constantThresholdRule_action _ _ _ _ _).mpr hx⟩
    exact ⟨ha, le_antisymm hr (π.stoppingTime_le_of_accepted _ _ _ _ _ ha)⟩

lemma constantThresholdRule_selected_count (t : ℝ) (x u : Fin n → ℝ)
    (hu : ∀ j, u j ≤ 1) :
    (∑ i, if (constantThresholdRule t n).ActualSelects () Finset.univ x u i then (1 : ℝ) else 0) =
      if ∃ i, t ≤ x i then 1 else 0 := by
  let π := constantThresholdRule t n
  change (∑ i, if π.ActualSelects () Finset.univ x u i then (1 : ℝ) else 0) =
    if ∃ i, t ≤ x i then 1 else 0
  by_cases h : ∃ i, t ≤ x i
  · obtain ⟨i, hi⟩ := h
    have ha : i ∈ π.accepted () Finset.univ x u :=
      (π.mem_accepted _ _ _ _ i).mpr ⟨Finset.mem_univ _, (constantThresholdRule_action _ _ _ _ _).mpr hi⟩
    obtain ⟨j, hj⟩ := π.exists_actualSelects_of_accepted () Finset.univ x u hu ⟨i, ha⟩
    rw [Finset.sum_eq_single j]
    · simp only [hj, if_true, if_pos (show ∃ i, t ≤ x i from ⟨i, hi⟩)]
    · intro l _ hlj
      have hno : ¬π.ActualSelects () Finset.univ x u l :=
        fun hl => hlj (π.actualSelects_unique _ _ _ _ hl hj)
      simp only [hno, if_false]
    · simp
  · have hno : ∀ i, ¬π.ActualSelects () Finset.univ x u i := by
      intro i hi
      have ha := (π.mem_accepted _ _ _ _ i |>.mp hi.1.1).2
      exact h ⟨i, (constantThresholdRule_action _ _ _ _ _).mp ha⟩
    simp only [hno, if_false, Finset.sum_const_zero, h]

lemma constantThresholdRule_reward_decomposition (t : ℝ) (x u : Fin n → ℝ)
    (hu : ∀ j, u j ≤ 1) (hinj : Function.Injective u) :
    (constantThresholdRule t n).reward () Finset.univ x u =
      t * (if ∃ i, t ≤ x i then 1 else 0) +
        ∑ i, max (x i - t) 0 * (if (constantThresholdRule t n).Reaches () x u i then 1 else 0) := by
  let π := constantThresholdRule t n
  change π.reward () Finset.univ x u = t * (if ∃ i, t ≤ x i then 1 else 0) +
    ∑ i, max (x i - t) 0 * (if π.Reaches () x u i then 1 else 0)
  have hi (i : Fin n) : (if π.ActualSelects () Finset.univ x u i then x i else 0) =
      t * (if π.ActualSelects () Finset.univ x u i then 1 else 0) +
        max (x i - t) 0 * (if π.Reaches () x u i then 1 else 0) := by
    by_cases ha : π.ActualSelects () Finset.univ x u i
    · obtain ⟨hx, hr⟩ := (constantThresholdRule_actualSelects_iff t x u hinj i).mp ha
      change π.Reaches () x u i at hr
      simp only [if_pos ha, if_pos hr, max_eq_left (sub_nonneg.mpr hx)]
      ring
    · by_cases hr : π.Reaches () x u i
      · have hx : x i < t := by
          by_contra hh
          exact ha ((constantThresholdRule_actualSelects_iff t x u hinj i).mpr ⟨le_of_not_gt hh, hr⟩)
        simp only [if_neg ha, if_pos hr, max_eq_right (sub_nonpos.mpr hx.le), zero_mul, mul_zero, add_zero]
      · simp only [if_neg ha, if_neg hr, mul_zero, add_zero]
  calc
    π.reward () Finset.univ x u = ∑ i, (t * (if π.ActualSelects () Finset.univ x u i then 1 else 0) +
        max (x i - t) 0 * (if π.Reaches () x u i then 1 else 0)) :=
      Finset.sum_congr rfl (fun i _ => hi i)
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum,
        constantThresholdRule_selected_count t x u hu]

end ProphetSecretary.Model
