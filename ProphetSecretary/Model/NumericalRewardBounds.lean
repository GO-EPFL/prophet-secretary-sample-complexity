import ProphetSecretary.Model.NumericalCompetitiveInstance
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.NormNum

/-! # Rational upper bounds for the finite Bellman recursions
Each step is rounded upward to a multiple of `10⁻⁶`. The finite inequalities
are checked by rational arithmetic in Lean; the marginal remains fixed.
-/
open MeasureTheory
namespace ProphetSecretary.Model.NumericalCompetitiveBound

private def iidUpper : ℕ → ℚ
  | 0 => 0 / 1
  | 1 => 48889 / 1000000
  | 2 => 19447 / 200000
  | 3 => 36261 / 250000
  | 4 => 96161 / 500000
  | 5 => 119537 / 500000
  | 6 => 285307 / 1000000
  | 7 => 165513 / 500000
  | 8 => 376237 / 1000000
  | 9 => 210473 / 500000
  | 10 => 232579 / 500000
  | 11 => 508879 / 1000000
  | 12 => 276057 / 500000
  | 13 => 594869 / 1000000
  | 14 => 637149 / 1000000
  | 15 => 678959 / 1000000
  | 16 => 45019 / 62500
  | 17 => 76119 / 100000
  | 18 => 801621 / 1000000
  | 19 => 841603 / 1000000
  | 20 => 881141 / 1000000
  | 21 => 11503 / 12500
  | 22 => 119863 / 125000
  | 23 => 997139 / 1000000
  | 24 => 1034949 / 1000000
  | 25 => 1072339 / 1000000
  | 26 => 1109313 / 1000000
  | 27 => 286469 / 250000
  | 28 => 1182033 / 1000000
  | 29 => 304447 / 250000
  | 30 => 626573 / 500000
  | _ => 0

private def standbyUpper : ℕ → ℚ
  | 0 => 4 / 5
  | 1 => 41 / 50
  | 2 => 209963 / 250000
  | 3 => 859557 / 1000000
  | 4 => 219779 / 250000
  | 5 => 898531 / 1000000
  | 6 => 917803 / 1000000
  | 7 => 936933 / 1000000
  | 8 => 477961 / 500000
  | 9 => 974771 / 1000000
  | 10 => 993481 / 1000000
  | 11 => 506027 / 500000
  | 12 => 1030491 / 1000000
  | 13 => 131099 / 125000
  | 14 => 1066959 / 1000000
  | 15 => 1084993 / 1000000
  | 16 => 68931 / 62500
  | 17 => 280167 / 250000
  | 18 => 227679 / 200000
  | 19 => 36187 / 31250
  | 20 => 294777 / 250000
  | 21 => 600751 / 500000
  | 22 => 306237 / 250000
  | 23 => 78079 / 62500
  | 24 => 1274299 / 1000000
  | 25 => 649963 / 500000
  | 26 => 331509 / 250000
  | 27 => 1352537 / 1000000
  | 28 => 1379351 / 1000000
  | 29 => 140641 / 100000
  | 30 => 358431 / 250000
  | _ => 0

private lemma marginalMaximum_monotone : Monotone (marginalMaximum marginal) := by
  intro x y hxy
  exact integral_mono (marginal_integrable _) (marginal_integrable _)
    (fun a ↦ max_le_max_left a hxy)

private lemma rounded_steps (m : ℕ) (hm : m < 30) :
    marginalMaximum marginal (iidUpper m : ℝ) ≤ (iidUpper (m + 1) : ℝ) ∧
      (max (4 / 5 : ℝ) (iidUpper (m + 1) : ℝ) + ((m : ℝ) + 1) *
        marginalMaximum marginal (standbyUpper m : ℝ)) / ((m : ℝ) + 2) ≤ (standbyUpper (m + 1) : ℝ) := by
  interval_cases m <;> norm_num [iidUpper, standbyUpper, marginalMaximum_eq]

private lemma reward_sequences_le_rounded (m : ℕ) (hm : m ≤ 30) :
    iidRewardSequence marginal m ≤ (iidUpper m : ℝ) ∧
      standbyRewardSequence marginal (4 / 5) m ≤ (standbyUpper m : ℝ) := by
  induction m with
  | zero => norm_num [iidRewardSequence, standbyRewardSequence, iidUpper, standbyUpper]
  | succ m ih =>
    have hm' : m < 30 := by omega
    obtain ⟨hS, hW⟩ := ih (by omega)
    obtain ⟨hStepS, hStepW⟩ := rounded_steps m hm'
    have hNextS := (marginalMaximum_monotone hS).trans hStepS
    refine ⟨hNextS, ?_⟩
    rw [standbyRewardSequence]
    apply le_trans _ hStepW
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact add_le_add (max_le_max_left _ hNextS)
      (mul_le_mul_of_nonneg_left (marginalMaximum_monotone hW) (by positivity))

lemma instance_optimalReward_upper : optimalScalarValue witnessInstance 1 0 ≤ (717 : ℝ) / 500 := by
  change optimalScalarValue (standbyIidInstance marginal marginal_nonnegative (4 / 5) (by norm_num) 30) 1 0 ≤ _
  rw [standbyIidInstance_optimalReward marginal marginal_nonnegative (marginal_integrable id) (4 / 5) (by norm_num) 30]
  exact (reward_sequences_le_rounded 30 (by omega)).2.trans (by norm_num [standbyUpper])

end ProphetSecretary.Model.NumericalCompetitiveBound
