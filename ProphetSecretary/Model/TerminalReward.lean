import ProphetSecretary.Model.MappedRewardPerformance
import ProphetSecretary.Model.ExcessValueMap

/-!
# Finite policies with a fixed terminal reward

The main online model still gives reward zero on no acceptance. This auxiliary
payoff gives a fixed reward a on that event, as in `lem:causal-poisson`, while
keeping the same history-dependent policies and stopping-time convention.
The all-policy upper comparison uses the proved mapped-reward Bellman identity.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma Policy.mappedReward_eq_of_actualSelects (π : Policy Seed n) (f : Fin n → ℝ → ℝ)
    (r : Seed) (D : Finset (Fin n)) (x u : Fin n → ℝ) {i : Fin n}
    (hi : π.ActualSelects r D x u i) : π.mappedReward f r D x u = f i (x i) := by
  unfold mappedReward
  rw [Finset.sum_eq_single i]
  · exact if_pos hi
  · intro j _ hji
    exact if_neg (fun hj => hji (π.actualSelects_unique r D x u hj hi))
  · simp

noncomputable def RandomizedPolicy.realizedTerminalReward (π : RandomizedPolicy n) (a : ℝ) (ω : π.World) : ℝ :=
  if ∃ i, π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i then π.realizedReward ω else a

noncomputable def RandomizedPolicy.terminalScalarObjective (π : RandomizedPolicy n)
    (P : Instance n) (a w c : ℝ) : ℝ :=
  ∫ ω : π.World, w * π.realizedTerminalReward a ω + c * π.realizedDuration ω ∂P.worldLaw π.seedLaw

lemma RandomizedPolicy.measurable_realizedTerminalReward (π : RandomizedPolicy n) (a : ℝ) :
    Measurable (π.realizedTerminalReward a) := by
  have hE : MeasurableSet {ω : π.World | ∃ i, π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i} := by
    rw [Set.setOf_exists]
    exact MeasurableSet.iUnion fun i => π.rule.measurableSet_actualSelects π.measurable_rule
      (by fun_prop) (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i
  exact Measurable.ite hE π.measurable_realizedReward measurable_const

lemma RandomizedPolicy.integrable_realizedTerminalReward (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a : ℝ) :
    Integrable (π.realizedTerminalReward a) (P.worldLaw π.seedLaw) := by
  apply ((π.integrable_realizedReward P hP).abs.add (integrable_const |a|)).mono'
    (π.measurable_realizedTerminalReward a).aestronglyMeasurable
  exact Filter.Eventually.of_forall fun ω => by
    change ‖if _ then π.realizedReward ω else a‖ ≤ |π.realizedReward ω| + |a|
    split_ifs <;> rw [Real.norm_eq_abs] <;> linarith [abs_nonneg a,abs_nonneg (π.realizedReward ω)]

lemma RandomizedPolicy.integrable_terminalScalarPayoff (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (a w c : ℝ) :
    Integrable (fun ω => w * π.realizedTerminalReward a ω + c * π.realizedDuration ω) (P.worldLaw π.seedLaw) :=
  ((π.integrable_realizedTerminalReward P hP a).const_mul w).add ((π.integrable_realizedDuration P).const_mul c)

lemma RandomizedPolicy.integrable_mappedReward_of_displacement (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (f : Fin n → ℝ → ℝ)
    (hf : ∀ i, Measurable (f i)) {h : ℝ} (hh : 0 ≤ h) (hdispl : ∀ i x, |f i x - x| ≤ h) :
    Integrable (fun ω : π.World => π.rule.mappedReward f ω.2.2 Finset.univ ω.1 ω.2.1) (P.worldLaw π.seedLaw) := by
  have hD := π.integrable_mappedRewardDifference P f hf hh hdispl
  apply ((π.integrable_realizedReward P hP).add hD).congr
  exact Filter.Eventually.of_forall fun ω => by
    change π.realizedReward ω + (π.rule.mappedReward f ω.2.2 Finset.univ ω.1 ω.2.1 - π.realizedReward ω) = _
    ring

lemma RandomizedPolicy.terminalReward_le_terminal_add_excess (π : RandomizedPolicy n) (a : ℝ) (ω : π.World) :
    π.realizedTerminalReward a ω ≤ a + π.rule.mappedReward (fun _ => excessValueMap a)
      ω.2.2 Finset.univ ω.1 ω.2.1 := by
  by_cases hs : ∃ i, π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i
  · obtain ⟨i, hi⟩ := hs
    unfold realizedTerminalReward
    rw [if_pos ⟨i,hi⟩]
    change π.rule.reward ω.2.2 Finset.univ ω.1 ω.2.1 ≤ _
    rw [π.rule.reward_eq_of_actualSelects ω.2.2 Finset.univ ω.1 ω.2.1 hi,
      π.rule.mappedReward_eq_of_actualSelects _ ω.2.2 Finset.univ ω.1 ω.2.1 hi]
    exact value_le_terminal_add_excess (ω.1 i)
  · unfold realizedTerminalReward
    rw [if_neg hs]
    have hz : π.rule.mappedReward (fun _ => excessValueMap a) ω.2.2 Finset.univ ω.1 ω.2.1 = 0 := by
      unfold Policy.mappedReward
      simp only [not_exists.mp hs, if_false, Finset.sum_const_zero]
    rw [hz,add_zero]

/-- A terminal payoff is bounded by the terminal constant plus the optimal
excess-offer value, for every admissible original-history policy. -/
theorem RandomizedPolicy.terminalScalarObjective_le_excessValue (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ} (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    π.terminalScalarObjective P a w c ≤ w * a + optimalScalarValue (P.excessOffers a) w c := by
  let f : Fin n → ℝ → ℝ := fun _ => excessValueMap a
  have hf : ∀ i, Measurable (f i) := fun _ => measurable_excessValueMap a
  have hd : ∀ i x, |f i x - x| ≤ a := fun _ x => excessValueMap_displacement ha x
  have hM := π.integrable_mappedReward_of_displacement P hP f hf ha hd
  have hJ : Integrable (fun ω : π.World => w * π.rule.mappedReward f ω.2.2 Finset.univ ω.1 ω.2.1 +
      c * π.realizedDuration ω) (P.worldLaw π.seedLaw) :=
    (hM.const_mul w).add ((π.integrable_realizedDuration P).const_mul c)
  have hbound := integral_mono (π.integrable_terminalScalarPayoff P hP a w c)
    ((integrable_const (w * a)).add hJ) (fun ω => by
      have h := mul_le_mul_of_nonneg_left (π.terminalReward_le_terminal_add_excess a ω) hw.le
      change w * π.realizedTerminalReward a ω + c * π.realizedDuration ω ≤
        w * a + (w * π.rule.mappedReward f ω.2.2 Finset.univ ω.1 ω.2.1 + c * π.realizedDuration ω)
      dsimp only [f]
      linarith only [h])
  change π.terminalScalarObjective P a w c ≤ ∫ ω : π.World,
    w * a + (w * π.rule.mappedReward f ω.2.2 Finset.univ ω.1 ω.2.1 + c * π.realizedDuration ω)
      ∂P.worldLaw π.seedLaw at hbound
  rw [integral_add (integrable_const (w * a)) hJ, integral_const] at hbound
  simp only [probReal_univ, one_smul] at hbound
  have hm := π.mappedScalarObjective_le_optimal P hP f hf
    (fun i => (P.nonnegative i).mono fun _ hx => excessValueMap_nonnegative hx) ha hw hc hd
  exact hbound.trans (add_le_add le_rfl hm)

end ProphetSecretary.Model
