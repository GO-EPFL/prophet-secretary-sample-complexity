import ProphetSecretary.Limiting.CountableMaskOrder
import ProphetSecretary.Limiting.CountableHistoryMask
import ProphetSecretary.Limiting.CountablePrefixLaw

/-!
# Exact finite continuation values for projected countable unseen masks

The masked prefix includes independent zero identities. Their value equality
with the physical retained subset is the proved finite causal zero simulation.
This identifies the finite continuation used by the actual threshold callback.
-/

open MeasureTheory Set
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma CountableInstance.finiteMaskState_continuation_eq_restrict (B : CountableInstance) (N : ℕ)
    (b : ℝ) (hb : (B.terminal : ℝ) < b) (keep : Fin N → Bool) {w c : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (u : ℝ≥0) :
    (B.finiteMaskState N b hb keep).continuationValue w c u =
      ((B.truncation N b hb).restrictIndividuals (finiteMaskSet keep)).continuationValue w c u := by
  let D := (B.truncation N b hb).remainingHorizon u
  calc
    _ = (D.zeroOutside (finiteMaskSet keep)).optimalScalarValue w (c*(u : ℝ)) :=
      B.finiteMaskState_value_eq_zeroOutside N b hb keep w (c*(u : ℝ)) u
    _ = (D.restrictIndividuals (finiteMaskSet keep)).optimalScalarValue w (c*(u : ℝ)) :=
      D.zeroOutside_value_eq_restrictIndividuals_with_terminal (finiteMaskSet keep) hw (mul_nonneg hc u.property)
    _ = _ := rfl

lemma CountableInstance.truncatedContinuationValue_eq_restrict (B : CountableInstance) (N : ℕ)
    (b : ℝ) (hb : (B.terminal : ℝ) < b) (keep : IndividualMask) {w c : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (u : ℝ≥0) :
    B.truncatedContinuationValue N b hb keep w c u =
      ((B.truncation N b hb).restrictIndividuals (finiteMaskSet (restrictIndividualMask N keep))).continuationValue w c u := by
  have he := congrArg (fun D : FiniteIntensityHybridInstance N => D.optimalScalarValue w (c*(u : ℝ)))
    (B.remainingState_truncation_eq keep u N b hb)
  exact he.trans (B.finiteMaskState_continuation_eq_restrict N b hb (restrictIndividualMask N keep) hw hc u)

lemma finiteMaskSet_restrict_unseenMask (N : ℕ) (H : IndividualHistory) :
    finiteMaskSet (restrictIndividualMask N (unseenMask H)) = Model.unseen (prefixHistory N H) := by
  ext i
  simp only [finiteMaskSet,Finset.mem_filter,Finset.mem_univ,true_and,restrictIndividualMask,
    unseenMask,decide_eq_true_eq,Model.unseen,prefixHistory]

lemma finiteMaskSet_restrict_eraseMask (N : ℕ) (keep : IndividualMask) (i : Fin N) :
    finiteMaskSet (restrictIndividualMask N (eraseMask keep i.val)) =
      (finiteMaskSet (restrictIndividualMask N keep)).erase i := by
  ext j
  by_cases hji : j = i
  · subst j
    simp only [finiteMaskSet,Finset.mem_filter,Finset.mem_univ,true_and,restrictIndividualMask,
      eraseMask,Function.update_self,reduceCtorEq,Finset.mem_erase,ne_eq,not_true_eq_false,false_and]
  · have hval : j.val ≠ i.val := by exact fun h => hji (Fin.ext h)
    simp only [finiteMaskSet,Finset.mem_filter,Finset.mem_univ,true_and,restrictIndividualMask,
      eraseMask,Function.update_of_ne hval,Finset.mem_erase,ne_eq,hji,not_false_eq_true,true_and]

end ProphetSecretary.Limiting
