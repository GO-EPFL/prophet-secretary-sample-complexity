import ProphetSecretary.Limiting.CountableConditionalSelection

/-!
# Canonical selection at an individual value of zero

The actual canonical acceptance callback rejects zero, independently of the
other values and clocks. Its individual conditional selection probability
therefore vanishes at zero, including when zero is a marginal atom.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

lemma valueRule_individualAction_zero (B : CountableInstance) (w c : ℝ)
    (i : ℕ) (v : CompleteWorld Unit) :
    (B.valueRule w c).candidateAction (replaceIndividualValue i (v,0)) (Sum.inl i)=false := by
  rw [B.valueRule_eq_markovAcceptance,countableMarkovRule_candidateAction_eq]
  simp only [valueMarkovAcceptance,candidatePoint,replaceIndividualValue,Function.update_self,
    lt_self_iff_false,false_and,decide_false]

lemma valueRule_not_selectsIndividual_zero (B : CountableInstance) (w c : ℝ)
    (i : ℕ) (v : CompleteWorld Unit) :
    ¬(B.valueRule w c).SelectsIndividual (replaceIndividualValue i (v,0)) i := by
  intro hSelected
  have hAction := hSelected.1.2.2
  rw [Equiv.symm_apply_apply,B.valueRule_individualAction_zero] at hAction
  exact Bool.false_ne_true hAction

theorem valueRule_conditionalSelectionAtValue_zero (B : CountableInstance) (w c : ℝ) (i : ℕ) :
    (B.valueRule w c).conditionalSelectionAtValue B (Measure.dirac ()) i 0=0 := by
  unfold CountableRule.conditionalSelectionAtValue
  have hIndicator (v : CompleteWorld Unit) :
      (B.valueRule w c).individualSelectionIndicator i (replaceIndividualValue i (v,0))=0 :=
    if_neg (B.valueRule_not_selectsIndividual_zero w c i v)
  simp_rw [hIndicator]
  exact integral_zero _ _

end ProphetSecretary.Limiting.CountableInstance
