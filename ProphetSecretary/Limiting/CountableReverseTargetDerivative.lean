import ProphetSecretary.Limiting.CountableIndividualTargetDerivative
import ProphetSecretary.Limiting.CountableBandTargetDerivative

/-!
# Reversing the actual likelihood parameter

A negative fixed-canonical duration response gives a positive original target
response. Reversing the parameter, with the same base callbacks and scalar
weights, gives the strictly negative target derivative needed by the statistical
experiment. Both likelihood paths already permit either sign near zero.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance

lemma hasDerivAt_reverse_parameter {f : ℝ → ℝ} {d : ℝ} (h : HasDerivAt f d 0) :
    HasDerivAt (fun θ => f (-θ)) (-d) 0 := by
  have hd := h.comp_of_eq (0 : ℝ) ((hasDerivAt_id (0 : ℝ)).neg) (by simp)
  change HasDerivAt (fun θ => f (-θ)) (d*(-1)) 0 at hd
  simpa only [mul_neg,mul_one] using hd

namespace CountableInstance

theorem exists_negative_reversed_individualTargetDerivative (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hSum : w+c=1) (hCritical : B.IsCritical w c)
    (i : ℕ) (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x|≤1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0)
    (hNegative : (B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i 0 1 h<0) :
    ∃ beta : ℝ, 0<beta ∧ HasDerivAt
      (fun θ => B.individualFixedTargetDifference hw hc i h hh hb hm (-θ)) (-beta) 0 := by
  have hd := hasDerivAt_reverse_parameter
    (B.hasDerivAt_individualFixedTargetDifference hw hc hSum hCritical i h hh hb hm)
  have hDNeg : (B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i 0 1 h/w<0 :=
    div_neg_of_neg_of_pos hNegative hw
  refine ⟨-((B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i 0 1 h/w),neg_pos.mpr hDNeg,?_⟩
  simpa only [neg_div,neg_neg] using hd

theorem exists_negative_reversed_bandTargetDerivative (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hSum : w+c=1) (hCritical : B.IsCritical w c)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    (hNegative : (B.valuePolicy hw hc).scalarBandLikelihoodDerivative S 0 1<0) :
    ∃ beta : ℝ, 0<beta ∧ HasDerivAt
      (fun θ => B.bandFixedTargetDifference hw hc hS hb hSub (-θ)) (-beta) 0 := by
  have hd := hasDerivAt_reverse_parameter
    (B.hasDerivAt_bandFixedTargetDifference hw hc hSum hCritical hS hb hSub)
  have hDNeg : (B.valuePolicy hw hc).scalarBandLikelihoodDerivative S 0 1/w<0 :=
    div_neg_of_neg_of_pos hNegative hw
  refine ⟨-((B.valuePolicy hw hc).scalarBandLikelihoodDerivative S 0 1/w),neg_pos.mpr hDNeg,?_⟩
  simpa only [neg_div,neg_neg] using hd

end CountableInstance
end ProphetSecretary.Limiting
