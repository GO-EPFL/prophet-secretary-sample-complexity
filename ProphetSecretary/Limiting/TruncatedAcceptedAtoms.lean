import ProphetSecretary.Limiting.TruncatedObserverActions
import ProphetSecretary.Limiting.CountableAcceptedPointMeasure

/-!
# Regrouping accepted atoms of the embedded truncated execution

The code enumeration is analytical. Actual acceptance predicates are identified
with the retained and anonymous callbacks supplied only with the allowed past.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed : Type*} {N : ℕ}

noncomputable def CountableRule.acceptedAtom (π : CountableRule Seed) (v : CompleteWorld Seed)
    (c : Candidate) : Measure Point :=
  if π.codeAccepted v (candidateEnumeration c) then Measure.dirac (candidatePoint v c) else 0

lemma pointMeasure_eq_acceptedAtoms (π : CountableRule Seed) (v : CompleteWorld Seed) :
    FirstAcceptance.pointMeasure π.codeAccepted codeTime codeValue v =
      Measure.sum (π.acceptedAtom v) := by
  let f : ℕ → Measure Point := fun i => if π.codeAccepted v i then Measure.dirac (codeTime v i,codeValue v i) else 0
  change Measure.sum f = _
  rw [← Measure.sum_comp_equiv candidateEnumeration f]
  apply congrArg Measure.sum
  funext c
  simp only [f,Function.comp_apply,codeTime,codeValue,codePoint,Equiv.symm_apply_apply,CountableRule.acceptedAtom]

lemma extended_individual_atom (π : HybridRule N Seed) (b : ℝ) (v : CompleteWorld Seed)
    (μ : FiniteMeasure Point)
    (hμ : (μ : Measure Point) = (bandCountingMeasure v.1).restrict (univ ×ˢ Ioi b)) (j : ℕ) :
    (extendTruncatedRule π b).acceptedAtom v (Sum.inl j) =
      if hj : j < N then
        (if π.individualMeasureAccepted (truncatedObserverWorld μ v) ⟨j,hj⟩ then
          Measure.dirac (v.2.2.1 j,v.2.1 j) else 0) else 0 := by
  by_cases hj : j < N
  · rw [dif_pos hj,CountableRule.acceptedAtom]
    rw [extended_individual_accepted_iff π b v μ hμ j hj]
    rfl
  · rw [dif_neg hj,CountableRule.acceptedAtom,if_neg (extended_individual_notAccepted π b v j hj)]

lemma extended_anonymous_atom (π : HybridRule N Seed) (b : ℝ) (v : CompleteWorld Seed)
    (μ : FiniteMeasure Point)
    (hμ : (μ : Measure Point) = (bandCountingMeasure v.1).restrict (univ ×ˢ Ioi b)) (k j : ℕ) :
    (extendTruncatedRule π b).acceptedAtom v (Sum.inr (k,j)) =
      if hj : j < (v.1 k).1 then
        (if b < ((v.1 k).2 ⟨j,hj⟩).2 ∧
          π.anonymousMeasureAccepted (truncatedObserverWorld μ v) ((v.1 k).2 ⟨j,hj⟩) then
          Measure.dirac ((v.1 k).2 ⟨j,hj⟩) else 0) else 0 := by
  by_cases hj : j < (v.1 k).1
  · rw [dif_pos hj,CountableRule.acceptedAtom]
    rw [extended_anonymous_accepted_iff π b v μ hμ k ⟨j,hj⟩]
    simp only [candidatePoint,configurationPoint,dif_pos hj]
  · have hnot : ¬(extendTruncatedRule π b).codeAccepted v (candidateEnumeration (Sum.inr (k,j))) := by
      intro h
      have hp := h.1
      exact hj (by simpa only [codePresent,Equiv.symm_apply_apply,candidatePresent] using hp)
    rw [dif_neg hj,CountableRule.acceptedAtom,if_neg hnot]

end ProphetSecretary.Limiting.CountableInstance
