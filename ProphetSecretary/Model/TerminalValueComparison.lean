import ProphetSecretary.Model.TerminalOptimalPolicy
import ProphetSecretary.Model.TerminalZeroWeight

/-!
# Finite terminal-reward comparisons

The policies and durations are unchanged when only the auxiliary default reward
changes. These comparisons concern the full randomized policy supremum.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.terminalReward_sub_reward_mem (π : RandomizedPolicy n) {a : ℝ}
    (ha : 0 ≤ a) (ω : π.World) :
    0 ≤ π.realizedTerminalReward a ω - π.realizedReward ω ∧
      π.realizedTerminalReward a ω - π.realizedReward ω ≤ a := by
  by_cases h : ∃ i, π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i
  · simp only [RandomizedPolicy.realizedTerminalReward,if_pos h,sub_self]
    exact ⟨le_rfl,ha⟩
  · have hz : π.realizedReward ω = 0 := π.rule.reward_eq_zero_of_no_actualSelection
      ω.2.2 Finset.univ ω.1 ω.2.1 (fun i hi => h ⟨i,hi⟩)
    simp only [RandomizedPolicy.realizedTerminalReward,if_neg h,hz,sub_zero]
    exact ⟨ha,le_rfl⟩

lemma RandomizedPolicy.scalarObjective_le_terminalScalarObjective (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) {a w : ℝ}
    (ha : 0 ≤ a) (hw : 0 ≤ w) (c : ℝ) :
    π.scalarObjective P w c ≤ π.terminalScalarObjective P a w c := by
  apply integral_mono (((π.integrable_realizedReward P hP).const_mul w).add
    ((π.integrable_realizedDuration P).const_mul c)) (π.integrable_terminalScalarPayoff P hP a w c)
  intro ω
  have he := mul_nonneg hw (π.terminalReward_sub_reward_mem ha ω).1
  change w*π.realizedReward ω+c*π.realizedDuration ω ≤
    w*π.realizedTerminalReward a ω+c*π.realizedDuration ω
  nlinarith only [he]

lemma RandomizedPolicy.terminalScalarObjective_le_scalarObjective_add (π : RandomizedPolicy n)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) {a w : ℝ}
    (ha : 0 ≤ a) (hw : 0 ≤ w) (c : ℝ) :
    π.terminalScalarObjective P a w c ≤ π.scalarObjective P w c + w*a := by
  have hJ : Integrable (fun ω : π.World => w*π.realizedReward ω+c*π.realizedDuration ω)
      (P.worldLaw π.seedLaw) := ((π.integrable_realizedReward P hP).const_mul w).add
    ((π.integrable_realizedDuration P).const_mul c)
  have h := integral_mono (π.integrable_terminalScalarPayoff P hP a w c)
    (hJ.add (integrable_const (w*a))) (fun ω => by
      have he := mul_le_mul_of_nonneg_left (π.terminalReward_sub_reward_mem ha ω).2 hw
      change w*π.realizedTerminalReward a ω+c*π.realizedDuration ω ≤
        w*π.realizedReward ω+c*π.realizedDuration ω+w*a
      nlinarith only [he])
  change π.terminalScalarObjective P a w c ≤ ∫ ω : π.World,
    (w*π.realizedReward ω+c*π.realizedDuration ω)+w*a ∂P.worldLaw π.seedLaw at h
  rw [integral_add hJ (integrable_const (w*a)),integral_const] at h
  have he : (∫ ω : π.World, w*π.realizedReward ω+c*π.realizedDuration ω ∂P.worldLaw π.seedLaw) =
      π.scalarObjective P w c := rfl
  rw [he] at h
  simpa only [probReal_univ,one_smul] using h

theorem Instance.terminal_value_comparison (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue P w c ≤ optimalTerminalScalarValue P a w c ∧
      optimalTerminalScalarValue P a w c ≤ optimalScalarValue P w c+w*a := by
  constructor
  · apply csSup_le (scalarValues_nonempty P w c)
    rintro v ⟨π,rfl⟩
    exact (π.scalarObjective_le_terminalScalarObjective P hP ha hw.le c).trans
      (le_csSup (terminalScalarValues_bddAbove P hP ha hw hc) ⟨π,rfl⟩)
  · apply csSup_le (terminalScalarValues_nonempty P a w c)
    rintro v ⟨π,rfl⟩
    exact (π.terminalScalarObjective_le_scalarObjective_add P hP ha hw.le c).trans
      (add_le_add (scalarObjective_le_optimal π P hP hw.le hc) le_rfl)

theorem Instance.terminal_value_comparison_nonnegative (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    optimalScalarValue P w c ≤ optimalTerminalScalarValue P a w c ∧
      optimalTerminalScalarValue P a w c ≤ optimalScalarValue P w c+w*a := by
  by_cases hw0 : w = 0
  · subst w
    rw [optimalTerminalScalarValue_zero_rewardWeight _ _ hc,optimalScalarValue_zero_rewardWeight _ hc]
    simp only [zero_mul,add_zero,le_refl,and_self]
  exact P.terminal_value_comparison hP ha (lt_of_le_of_ne hw (Ne.symm hw0)) hc

end ProphetSecretary.Model
