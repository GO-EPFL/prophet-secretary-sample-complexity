import ProphetSecretary.Model.Outcome
import Mathlib.Order.Fin.Basic

/-!
# Ignoring additional offers

A policy on a subset of identities extends to a larger instance by projecting observed
histories and rejecting the other identities. The construction is causal even when the
extra observations carry values, times, and identities. This is the policy simulation
needed for monotonicity under adding unseen options.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {Seed : Type*} {m n : ℕ}

/-- Relabel the observable past along an injection of identities. -/
def projectHistory (e : Fin m ↪ Fin n) (h : History n) : History m := fun i => h (e i)

/-- Ignore every additional identity, including its value and its arrival time. -/
noncomputable def Policy.ignoreExtras (π : Policy Seed m) (e : Fin m ↪ Fin n) :
    Policy Seed n where
  decide r t j x h := Decidable.decide (∃ i, e i = j ∧ π.decide r t i x (projectHistory e h) = true)

theorem projectHistory_history (e : Fin m ↪ Fin n) (x u : Fin n → ℝ) (t : ℝ) :
    projectHistory e (history Finset.univ x u t) =
      history Finset.univ (x ∘ e) (u ∘ e) t := by
  funext i
  simp [projectHistory, history]

theorem Policy.ignoreExtras_mem_accepted (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) (j : Fin n) :
    j ∈ (π.ignoreExtras e).accepted r Finset.univ x u ↔
      ∃ i, e i = j ∧ i ∈ π.accepted r Finset.univ (x ∘ e) (u ∘ e) := by
  simp only [Policy.mem_accepted, Finset.mem_univ, true_and, Policy.action,
    Policy.ignoreExtras, decide_eq_true_eq]
  constructor
  · rintro ⟨i, rfl, hi⟩
    exact ⟨i, rfl, by simpa only [projectHistory_history, Function.comp_apply] using hi⟩
  · rintro ⟨i, rfl, hi⟩
    exact ⟨i, rfl, by simpa only [projectHistory_history, Function.comp_apply] using hi⟩

theorem Policy.ignoreExtras_accepted_times (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) :
    ((π.ignoreExtras e).accepted r Finset.univ x u).image u =
      (π.accepted r Finset.univ (x ∘ e) (u ∘ e)).image (u ∘ e) := by
  ext t
  simp only [Finset.mem_image, π.ignoreExtras_mem_accepted]
  constructor
  · rintro ⟨j, ⟨i, rfl, hi⟩, ht⟩
    exact ⟨i, hi, ht⟩
  · rintro ⟨i, hi, ht⟩
    exact ⟨e i, ⟨i, rfl, hi⟩, ht⟩

/-- Adding ignored offers leaves duration exactly unchanged on every complete path. -/
theorem Policy.ignoreExtras_stoppingTime (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) :
    (π.ignoreExtras e).stoppingTime r Finset.univ x u =
      π.stoppingTime r Finset.univ (x ∘ e) (u ∘ e) := by
  unfold Policy.stoppingTime Policy.stopTimes
  simp only [π.ignoreExtras_accepted_times]

theorem Policy.ignoreExtras_selects_iff (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin m) :
    (π.ignoreExtras e).Selects r Finset.univ x u (e i) ↔
      π.Selects r Finset.univ (x ∘ e) (u ∘ e) i := by
  simp only [Policy.Selects, π.ignoreExtras_mem_accepted, π.ignoreExtras_stoppingTime]
  constructor
  · rintro ⟨⟨j, hj, ha⟩, ht⟩
    have hji := e.injective hj
    subst j
    exact ⟨ha, ht⟩
  · rintro ⟨ha, ht⟩
    exact ⟨⟨i, rfl, ha⟩, ht⟩

theorem Policy.ignoreExtras_selects_exists (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) {j : Fin n}
    (hj : (π.ignoreExtras e).Selects r Finset.univ x u j) :
    ∃ i, e i = j ∧ π.Selects r Finset.univ (x ∘ e) (u ∘ e) i := by
  obtain ⟨i, hi, _⟩ := (π.ignoreExtras_mem_accepted e r x u j).mp hj.1
  refine ⟨i, hi, ?_⟩
  apply (π.ignoreExtras_selects_iff e r x u i).mp
  simpa only [hi] using hj

/-- With distinct base clocks, the reward is unchanged even for an arbitrary relabeling. -/
theorem Policy.ignoreExtras_reward (π : Policy Seed m) (e : Fin m ↪ Fin n)
    (r : Seed) (x u : Fin n → ℝ) (hu : Function.Injective (u ∘ e)) :
    (π.ignoreExtras e).reward r Finset.univ x u =
      π.reward r Finset.univ (x ∘ e) (u ∘ e) := by
  by_cases h : ∃ i, π.Selects r Finset.univ (x ∘ e) (u ∘ e) i
  · obtain ⟨i, hi⟩ := h
    have hlarge : (π.ignoreExtras e).ActualSelects r Finset.univ x u (e i) := by
      refine ⟨(π.ignoreExtras_selects_iff e r x u i).mpr hi, ?_⟩
      intro j hj
      obtain ⟨k, hk, hks⟩ := π.ignoreExtras_selects_exists e r x u hj
      have hik := π.selects_unique r Finset.univ (x ∘ e) (u ∘ e) hu hi hks
      subst k
      exact le_of_eq hk
    rw [(π.ignoreExtras e).reward_eq_of_actualSelects r Finset.univ x u hlarge,
      π.reward_eq_of_selects r Finset.univ (x ∘ e) (u ∘ e) hu hi]
    rfl
  · have hlarge : ∀ j, ¬(π.ignoreExtras e).Selects r Finset.univ x u j := by
      intro j hj
      obtain ⟨i, _, hi⟩ := π.ignoreExtras_selects_exists e r x u hj
      exact h ⟨i, hi⟩
    rw [(π.ignoreExtras e).reward_eq_zero_of_no_selection r Finset.univ x u hlarge,
      π.reward_eq_zero_of_no_selection r Finset.univ (x ∘ e) (u ∘ e) (fun i hi => h ⟨i, hi⟩)]

/-- An order-preserving identity injection preserves the literal tie-breaking rule. -/
theorem Policy.ignoreExtras_actualSelects_iff (π : Policy Seed m) (e : Fin m ↪o Fin n)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin m) :
    (π.ignoreExtras e.toEmbedding).ActualSelects r Finset.univ x u (e i) ↔
      π.ActualSelects r Finset.univ (x ∘ e) (u ∘ e) i := by
  constructor
  · intro hi
    refine ⟨(π.ignoreExtras_selects_iff e.toEmbedding r x u i).mp hi.1, ?_⟩
    intro j hj
    exact e.le_iff_le.mp (hi.2 (e j) ((π.ignoreExtras_selects_iff e.toEmbedding r x u j).mpr hj))
  · intro hi
    refine ⟨(π.ignoreExtras_selects_iff e.toEmbedding r x u i).mpr hi.1, ?_⟩
    intro j hj
    obtain ⟨k, hk, hks⟩ := π.ignoreExtras_selects_exists e.toEmbedding r x u hj
    rw [← hk]
    exact e.monotone (hi.2 k hks)

/-- In particular, appending ignored variables preserves reward on every outcome,
including tied clocks, because the original identities retain their order. -/
theorem Policy.ignoreExtras_reward_orderEmbedding (π : Policy Seed m) (e : Fin m ↪o Fin n)
    (r : Seed) (x u : Fin n → ℝ) :
    (π.ignoreExtras e.toEmbedding).reward r Finset.univ x u =
      π.reward r Finset.univ (x ∘ e) (u ∘ e) := by
  by_cases h : ∃ i, π.ActualSelects r Finset.univ (x ∘ e) (u ∘ e) i
  · obtain ⟨i, hi⟩ := h
    have hlarge := (π.ignoreExtras_actualSelects_iff e r x u i).mpr hi
    rw [(π.ignoreExtras e.toEmbedding).reward_eq_of_actualSelects r Finset.univ x u hlarge,
      π.reward_eq_of_actualSelects r Finset.univ (x ∘ e) (u ∘ e) hi]
    rfl
  · have hlarge : ∀ j, ¬(π.ignoreExtras e.toEmbedding).ActualSelects r Finset.univ x u j := by
      intro j hj
      obtain ⟨i, hi, _⟩ := π.ignoreExtras_selects_exists e.toEmbedding r x u hj.1
      have hs : (π.ignoreExtras e.toEmbedding).ActualSelects r Finset.univ x u (e i) := by
        rw [show e i = j from hi]
        exact hj
      exact h ⟨i, (π.ignoreExtras_actualSelects_iff e r x u i).mp hs⟩
    rw [(π.ignoreExtras e.toEmbedding).reward_eq_zero_of_no_actualSelection r Finset.univ x u hlarge,
      π.reward_eq_zero_of_no_actualSelection r Finset.univ (x ∘ e) (u ∘ e) (fun i hi => h ⟨i, hi⟩)]

variable [MeasurableSpace Seed]

/-- Projection of the full observable history is measurable. -/
theorem measurable_projectHistory (e : Fin m ↪ Fin n) : Measurable (projectHistory e) := by
  apply measurable_pi_lambda
  intro i
  exact measurable_pi_apply (e i)

/-- The simulation preserves joint measurability of the policy's action. -/
theorem Policy.ignoreExtras_isMeasurable (π : Policy Seed m) (hπ : π.IsMeasurable)
    (e : Fin m ↪ Fin n) : (π.ignoreExtras e).IsMeasurable := by
  apply measurable_to_bool
  change MeasurableSet {z : Seed × (ℝ × (Fin n × (ℝ × History n))) |
    Decidable.decide (∃ i, e i = z.2.2.1 ∧
      π.decide z.1 z.2.1 i z.2.2.2.1 (projectHistory e z.2.2.2.2) = true) = true}
  simp only [decide_eq_true_eq]
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro i
  apply (measurableSet_eq_fun measurable_const measurable_snd.snd.fst).inter
  have hm : Measurable (fun z : Seed × (ℝ × (Fin n × (ℝ × History n))) =>
      π.decide z.1 z.2.1 i z.2.2.2.1 (projectHistory e z.2.2.2.2)) := by
    exact hπ.comp (measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_const.prodMk
      (measurable_snd.snd.snd.fst.prodMk
        ((measurable_projectHistory e).comp measurable_snd.snd.snd.snd)))))
  exact hm (measurableSet_singleton true)

end ProphetSecretary.Model
