import ProphetSecretary.Model.ExcessMeasure
import ProphetSecretary.Limiting.FiniteArrayEvaluation

/-!
# Excess transformations of finite retained/anonymous arrays

The actual coordinate pushforward commutes with concatenation. The mapped mark
law is an analytical nonnegative probability law and may have a zero atom.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Limiting

open ProphetSecretary.Model

variable {n N : ℕ}

lemma excessOffers_appendIID (P : Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (N : ℕ) (a : ℝ) :
    (appendIID P κ hκ N).excessOffers a = appendIID (P.excessOffers a) (excessLaw κ a)
      (excessLaw_nonnegative κ hκ a) N := by
  apply Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases with
  | left i => simp only [Instance.excessOffers,Instance.mapValues,appendIID,Fin.addCases_left]
  | right j => simp only [Instance.excessOffers,Instance.mapValues,appendIID,Fin.addCases_right,excessLaw]

end ProphetSecretary.Limiting
