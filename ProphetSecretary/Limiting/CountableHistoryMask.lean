import ProphetSecretary.Limiting.CountableObservations
import ProphetSecretary.Limiting.CountableRemainingState
import ProphetSecretary.Model.ContinuationTransport

/-!
# The unseen identity mask of an observable countable history

A zero-valued arrival is a present observation and removes that identity from
the unseen mask. The mask contains no future values or anonymous labels.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def unseenMask (H : IndividualHistory) : IndividualMask := fun i => decide (H i = none)

def eraseMask (keep : IndividualMask) (i : ℕ) : IndividualMask := Function.update keep i false

lemma measurable_unseenMask : Measurable unseenMask := by
  apply measurable_pi_lambda
  intro i
  apply measurable_to_bool
  change MeasurableSet {H : IndividualHistory | decide (H i = none) = true}
  simp only [decide_eq_true_eq]
  have hEval : Measurable (fun H : IndividualHistory => H i) := measurable_pi_apply i
  exact Model.measurableSet_observation_none.preimage hEval

lemma measurable_eraseMask : Measurable (fun z : IndividualMask × ℕ => eraseMask z.1 z.2) := by
  apply measurable_pi_lambda
  intro j
  have heq : MeasurableSet {z : IndividualMask × ℕ | z.2 = j} := measurable_snd (measurableSet_singleton j)
  have hKeep : Measurable (fun z : IndividualMask × ℕ => z.1 j) := (measurable_pi_apply j).comp measurable_fst
  have hFn : (fun z : IndividualMask × ℕ => eraseMask z.1 z.2 j) =
      (fun z => if z.2 = j then false else z.1 j) := by
    funext z
    by_cases hz : z.2 = j
    · rw [hz]
      simp [eraseMask]
    · simp only [eraseMask,Function.update_of_ne (Ne.symm hz),if_neg hz]
  rw [hFn]
  exact Measurable.ite heq measurable_const hKeep

lemma unseenMask_some (H : IndividualHistory) (i : ℕ) (p : Point) (hi : H i = some p) : unseenMask H i = false := by
  simp only [unseenMask,hi,reduceCtorEq,decide_false]

lemma unseenMask_individualHistory (x u : ℕ → ℝ) (t : ℝ) (i : ℕ) :
    unseenMask (individualHistory x u t) i = decide (t ≤ u i) := by
  by_cases ht : u i < t
  · simp only [unseenMask,individualHistory,if_pos ht,reduceCtorEq,decide_false,not_le.mpr ht]
  · simp only [unseenMask,individualHistory,if_neg ht,decide_true,le_of_not_gt ht]

end ProphetSecretary.Limiting.CountableInstance
