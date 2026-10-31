import ProphetSecretary.Model.BellmanResidual
import ProphetSecretary.Model.ValueTransform

/-!
# Bellman losses with transformed rewards and original observations

The policy observes the original offers and their full histories. The mapped
reward changes only the payoff at the selected occurrence. This separates an
analytical value perturbation from the information available to the policy.
Paper correspondence: `upmom:transport` and the tagged-value envelope argument.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma Policy.actualSelects_iff_reaches_and_action (π : Policy Seed n) (r : Seed)
    (x u : Fin n → ℝ) (hu : Function.Injective u) (i : Fin n) :
    π.ActualSelects r Finset.univ x u i ↔ π.Reaches r x u i ∧ π.action r Finset.univ x u i = true := by
  rw [π.actualSelects_iff_selects r Finset.univ x u hu i]
  constructor
  · intro hi
    exact ⟨hi.2.le, (π.mem_accepted r Finset.univ x u i).mp hi.1 |>.2⟩
  · rintro ⟨hr, ha⟩
    have hacc := (π.mem_accepted r Finset.univ x u i).mpr ⟨Finset.mem_univ i, ha⟩
    exact ⟨hacc, le_antisymm hr (π.stoppingTime_le_of_accepted r Finset.univ x u i hacc)⟩

noncomputable def Policy.mappedReward (π : Policy Seed n) (f : Fin n → ℝ → ℝ)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if π.ActualSelects r D x u i then f i (x i) else 0

lemma Policy.mappedReward_affine (π : Policy Seed n) (f : Fin n → ℝ → ℝ) (h : ℝ)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) :
    π.mappedReward (fun i a => a + h * f i a) r D x u = π.reward r D x u + h * π.mappedReward f r D x u := by
  unfold Policy.mappedReward Policy.reward
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  by_cases hi : π.ActualSelects r D x u i
  · simp only [if_pos hi]
  · simp only [if_neg hi, mul_zero, add_zero]

lemma Policy.mappedReward_abs_difference_le (π : Policy Seed n) (f : Fin n → ℝ → ℝ)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) {h : ℝ} (hh : 0 ≤ h)
    (hdispl : ∀ i, |f i (x i) - x i| ≤ h) :
    |π.mappedReward f r D x u - π.reward r D x u| ≤ h := by
  by_cases hs : ∃ i, π.ActualSelects r D x u i
  · obtain ⟨i, hi⟩ := hs
    have hm : π.mappedReward f r D x u = f i (x i) := by
      unfold Policy.mappedReward
      rw [Finset.sum_eq_single i]
      · simp only [if_pos hi]
      · intro j _ hji
        have hj : ¬π.ActualSelects r D x u j := fun hj => hji (π.actualSelects_unique r D x u hj hi)
        simp only [if_neg hj]
      · simp
    rw [hm, π.reward_eq_of_actualSelects r D x u hi]
    exact hdispl i
  · have hns : ∀ i, ¬π.ActualSelects r D x u i := fun i hi => hs ⟨i, hi⟩
    simp only [Policy.mappedReward, hns, if_false, Finset.sum_const_zero,
      π.reward_eq_zero_of_no_actualSelection r D x u hns, sub_self, abs_zero]
    exact hh

noncomputable def Policy.mappedArrivalLoss (π : Policy Seed n) (Q : Instance n)
    (f : Fin n → ℝ → ℝ) (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) (i : Fin n) : ℝ :=
  max (w * f i (x i)) (Q.continuationAtArrival w c x u i) -
    if π.action r Finset.univ x u i = true then w * f i (x i) else Q.continuationAtArrival w c x u i

noncomputable def Policy.mappedReachedLoss (π : Policy Seed n) (Q : Instance n)
    (f : Fin n → ℝ → ℝ) (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if π.Reaches r x u i then π.mappedArrivalLoss Q f w c r x u i else 0

noncomputable def Policy.reachedMaxDifference (π : Policy Seed n) (Q : Instance n)
    (f : Fin n → ℝ → ℝ) (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, if π.Reaches r x u i then
    max (w * x i) (Q.continuationAtArrival w c x u i) -
      max (w * f i (x i)) (Q.continuationAtArrival w c x u i) else 0

lemma Policy.mappedArrivalLoss_nonnegative (π : Policy Seed n) (Q : Instance n)
    (f : Fin n → ℝ → ℝ) (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) (i : Fin n) :
    0 ≤ π.mappedArrivalLoss Q f w c r x u i := by
  unfold Policy.mappedArrivalLoss
  split_ifs
  · exact sub_nonneg.mpr (le_max_left _ _)
  · exact sub_nonneg.mpr (le_max_right _ _)

lemma Policy.mappedReachedLoss_nonnegative (π : Policy Seed n) (Q : Instance n)
    (f : Fin n → ℝ → ℝ) (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) :
    0 ≤ π.mappedReachedLoss Q f w c r x u := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact π.mappedArrivalLoss_nonnegative Q f w c r x u i
  · exact le_rfl

/-- Exact algebra before taking expectations. Reach/action indicators become
selection indicators only after invoking distinct clocks and the actual execution. -/
theorem Policy.mappedLoss_difference_identity (π : Policy Seed n) (Q : Instance n)
    (f : Fin n → ℝ → ℝ) (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) (hu : Function.Injective u) :
    π.reachedBellmanLoss Q w c r x u - π.mappedReachedLoss Q f w c r x u =
      π.reachedMaxDifference Q f w c r x u + w * (π.mappedReward f r Finset.univ x u - π.reward r Finset.univ x u) := by
  unfold Policy.reachedBellmanLoss Policy.mappedReachedLoss Policy.reachedMaxDifference
    Policy.mappedReward Policy.reward
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hs := π.actualSelects_iff_reaches_and_action r x u hu i
  by_cases hr : π.Reaches r x u i
  · by_cases ha : π.action r Finset.univ x u i = true
    · have hsel := hs.mpr ⟨hr, ha⟩
      simp only [if_pos hr, if_pos hsel, Policy.arrivalBellmanLoss, Policy.mappedArrivalLoss, if_pos ha]
      ring
    · have hsel : ¬π.ActualSelects r Finset.univ x u i := fun hi => ha (hs.mp hi).2
      simp only [if_pos hr, if_neg hsel, Policy.arrivalBellmanLoss, Policy.mappedArrivalLoss, if_neg ha]
      ring
  · have hsel : ¬π.ActualSelects r Finset.univ x u i := fun hi => hr (hs.mp hi).1
    simp only [if_neg hr, if_neg hsel, sub_self, mul_zero, add_zero]

section Measurability

variable {Ω : Type*} [MeasurableSpace Ω] [MeasurableSpace Seed]

lemma Policy.measurable_mappedReward (π : Policy Seed n) (hπ : π.IsMeasurable)
    (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    {r : Ω → Seed} {x u : Ω → Fin n → ℝ} (hr : Measurable r)
    (hx : ∀ i, Measurable fun ω => x ω i) (hu : ∀ i, Measurable fun ω => u ω i)
    (D : Finset (Fin n)) : Measurable (fun ω => π.mappedReward f (r ω) D (x ω) (u ω)) := by
  apply Finset.measurable_sum
  intro i _
  exact Measurable.ite (π.measurableSet_actualSelects hπ hr hx hu D i) ((hf i).comp (hx i)) measurable_const

end Measurability
end ProphetSecretary.Model
