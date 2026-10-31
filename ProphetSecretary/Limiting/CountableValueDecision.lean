import ProphetSecretary.Limiting.CountableValueTies

/-!
# Actual countable acceptance decisions before the terminal time

Positive waiting value makes the positive-value gate redundant before time1.
The remaining comparison is exactly current weighted reward versus child value.
-/

open MeasureTheory
open scoped Classical NNReal

namespace ProphetSecretary.Limiting.CountableInstance

lemma valueRule_candidateAction_iff_preterminal (B : CountableInstance) {w c : ℝ}
    (hw : 0 < w) (hc : 0 < c) (v : CompleteWorld Unit) (j : Candidate)
    (ht : (candidatePoint v j).1 < 1) :
    (B.valueRule w c).candidateAction v j = true ↔
      B.valueContinuationAtCandidate w c v j ≤ w*(candidatePoint v j).2 := by
  have hPositive : 0 < B.valueContinuationAtCandidate w c v j :=
    (B.clockProfile_pos v.2.2.1 (candidateKind j) hw hc ht).trans_eq
      (B.valueContinuationAtCandidate_eq_clockProfile w c v j).symm
  constructor
  · intro hAction
    cases j <;> exact (of_decide_eq_true hAction).2
  · intro hValue
    have hx : 0 < (candidatePoint v j).2 := by
      by_contra hn
      exact (not_le_of_gt hPositive) (hValue.trans
        (mul_nonpos_of_nonneg_of_nonpos hw.le (not_lt.mp hn)))
    cases j <;> exact decide_eq_true ⟨hx,hValue⟩

end ProphetSecretary.Limiting.CountableInstance
