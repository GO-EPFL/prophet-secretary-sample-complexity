import ProphetSecretary.Limiting.CountableSelectedTags
import ProphetSecretary.Limiting.CountablePositivePairs
import ProphetSecretary.Stability.SelectedOccurrence

/-!
# Selected-tag control from the actual full outcome error

The close-pair event counts every positive occurrence, including offers after
stopping. Its probability and the shared-input outcome error yield constants
depending only on the tag bound, cutoff and positive-level tail count.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma RandomizedCountablePolicy.selectedTag_stability_bound {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (hZero : B.terminal=0) {w c D b η L : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hD : 0 ≤ D) (hb : 0 < b) (hη : 0 < η)
    (hL : (B.totalTailMass (b/2)).toReal ≤ L)
    (tag : CountableTags π.Seed) (hTag : tag.IsMeasurable)
    (hBound : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, ∀ i, |tag v i| ≤ D)
    (hTagZero : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, ∀ i, codeValue v i < b → tag v i=0) :
    π.expectedSelectedTagError w c tag ≤ 2*D*(2*π.expectedValueOutcomeError w c/b+
      π.expectedValueOutcomeError w c/η+2*η*(1+L)^2) := by
  have h := π.rule.integral_selectedTagDifference_le π.measurable_rule B hZero π.seedLaw
    hw hc hD hb hη tag hTag hBound hTagZero
  have hPair := B.closePositivePair_probability hZero π.seedLaw (half_pos hb) hη.le
  have hTail0 : 0 ≤ (B.totalTailMass (b/2)).toReal := ENNReal.toReal_nonneg
  have hPoly : (B.totalTailMass (b/2)).toReal^2+(B.totalTailMass (b/2)).toReal ≤ (1+L)^2 := by nlinarith
  have hPair' := hPair.trans (mul_le_mul_of_nonneg_left hPoly (show 0 ≤ 2*η by positivity))
  exact h.trans (mul_le_mul_of_nonneg_left (add_le_add le_rfl hPair') (show 0 ≤ 2*D by positivity))

theorem RandomizedCountablePolicy.selectedTag_stability_of_outcome_bound {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (hZero : B.terminal=0) {w c D b L W : ℝ}
    (hw : 0 ≤ w) (hc : 0 ≤ c) (hD : 0 ≤ D) (hb : 0 < b)
    (hL : (B.totalTailMass (b/2)).toReal ≤ L) (hW : π.expectedValueOutcomeError w c ≤ W)
    (tag : CountableTags π.Seed) (hTag : tag.IsMeasurable)
    (hBound : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, ∀ i, |tag v i| ≤ D)
    (hTagZero : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, ∀ i, codeValue v i < b → tag v i=0) :
    π.expectedSelectedTagError w c tag ≤ Model.selectedTagErrorBound D b (1+L) W := by
  have hBase : π.expectedSelectedTagError w c tag ≤ Model.selectedTagErrorBound D b (1+L)
      (π.expectedValueOutcomeError w c) :=
    Model.selectedTag_error_optimize hD hb (π.expectedValueOutcomeError_nonnegative w c)
      (fun _ hη => π.selectedTag_stability_bound hZero hw hc hD hb hη hL tag hTag hBound hTagZero)
  exact hBase.trans (Model.selectedTagErrorBound_monotone hD hb hW)

end ProphetSecretary.Limiting
