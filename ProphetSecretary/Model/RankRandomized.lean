import ProphetSecretary.Model.RankMeasurability
import ProphetSecretary.Model.ScalarObjectives

/-!
# General randomized rank policies

The independent auxiliary seed may have any measurable probability law.
The online world is the product of independent offer values, a uniform
permutation, and that seed. Reward and reach have their usual rank semantics;
no physical duration is assigned to the rank representation.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma RankPolicy.reward_nonnegative (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (hx : ∀ i, 0 ≤ x i) : 0 ≤ π.reward r p x := by
  apply Finset.sum_nonneg
  intro i _
  split_ifs
  · exact hx i
  · exact le_rfl

lemma RankPolicy.reward_eq_of_selects (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) {i : Fin n} (hi : π.Selects r p x i) :
    π.reward r p x = x i := by
  unfold RankPolicy.reward
  rw [Finset.sum_eq_single i]
  · simp only [if_pos hi]
  · intro j _ hji
    have hj : ¬π.Selects r p x j := fun hj => hji (π.selects_unique r p x hj hi)
    simp only [if_neg hj]
  · simp

lemma RankPolicy.reward_le_maximum (π : RankPolicy Seed n) (r : Seed)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : π.reward r p x ≤ Instance.maximum x := by
  by_cases h : ∃ i, π.Selects r p x i
  · obtain ⟨i,hi⟩ := h
    rw [π.reward_eq_of_selects r p x hi]
    exact Instance.le_maximum x i
  · have hz : π.reward r p x = 0 := by
      unfold RankPolicy.reward
      exact Finset.sum_eq_zero fun i _ => if_neg (fun hi => h ⟨i,hi⟩)
    rw [hz]
    exact Instance.maximum_nonnegative x

structure RandomizedRankPolicy (n : ℕ) where
  Seed : Type
  [seedSpace : MeasurableSpace Seed]
  seedLaw : Measure Seed
  [probability : IsProbabilityMeasure seedLaw]
  rule : RankPolicy Seed n
  measurable_rule : rule.IsMeasurable

attribute [instance] RandomizedRankPolicy.seedSpace RandomizedRankPolicy.probability

namespace RandomizedRankPolicy

abbrev World (π : RandomizedRankPolicy n) := (Fin n → ℝ) × (Equiv.Perm (Fin n) × π.Seed)

noncomputable def worldLaw (π : RandomizedRankPolicy n) (P : Instance n) : Measure π.World :=
  P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod π.seedLaw)

instance worldLaw_probability (π : RandomizedRankPolicy n) (P : Instance n) : IsProbabilityMeasure (π.worldLaw P) := by
  unfold worldLaw
  infer_instance

noncomputable def realizedReward (π : RandomizedRankPolicy n) (ω : π.World) : ℝ :=
  π.rule.reward ω.2.2 ω.2.1 ω.1

lemma measurable_realizedReward (π : RandomizedRankPolicy n) : Measurable π.realizedReward :=
  π.rule.measurable_reward π.measurable_rule (measurable_snd.comp measurable_snd)
    (measurable_fst.comp measurable_snd) (fun i => (measurable_pi_apply i).comp measurable_fst)

lemma integrable_realizedReward (π : RandomizedRankPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) : Integrable π.realizedReward (π.worldLaw P) := by
  have hv : MeasurePreserving (fun ω : π.World => ω.1) (π.worldLaw P) P.valuesLaw := measurePreserving_fst
  apply (hv.integrable_comp_of_integrable hP).mono' π.measurable_realizedReward.aestronglyMeasurable
  filter_upwards [hv.quasiMeasurePreserving.ae P.ae_nonnegative] with ω hω
  change ‖π.rule.reward ω.2.2 ω.2.1 ω.1‖ ≤ Instance.maximum ω.1
  rw [Real.norm_eq_abs,abs_of_nonneg (π.rule.reward_nonnegative ω.2.2 ω.2.1 ω.1 hω)]
  exact π.rule.reward_le_maximum ω.2.2 ω.2.1 ω.1

noncomputable def expectedReward (π : RandomizedRankPolicy n) (P : Instance n) : ℝ :=
  ∫ ω, π.realizedReward ω ∂π.worldLaw P

end RandomizedRankPolicy

end ProphetSecretary.Model
