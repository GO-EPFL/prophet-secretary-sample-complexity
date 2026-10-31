import ProphetSecretary.Limiting.HybridExcessState
import ProphetSecretary.Limiting.PoissonizedFamily
import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Model.ExcessPositiveTail

/-!
# Excess transformations commute with Poissonization

Only the strictly positive pushforward intensity is used in the hybrid state.
The preimage of a positive excess value is already positive, so taking each
original positive restriction before the pushforward does not change it.
This proves the actual intensity identity, not an information-erasure premise.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

variable {n m : ℕ}

lemma excessOffers_appendIndependent (P : Model.Instance n) (R : Model.Instance m) (a : ℝ) :
    (P.appendIndependent R).excessOffers a = (P.excessOffers a).appendIndependent (R.excessOffers a) := by
  apply Model.Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases with
  | left i => simp only [Model.Instance.excessOffers,Model.Instance.mapValues,Model.Instance.appendIndependent,Fin.addCases_left]
  | right j => simp only [Model.Instance.excessOffers,Model.Instance.mapValues,Model.Instance.appendIndependent,Fin.addCases_right]

lemma excessOffers_bounded (P : Model.Instance n) {a H : ℝ} (ha : 0 ≤ a)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) : ∀ i, ∀ᵐ y ∂(P.excessOffers a).law i, y ≤ H := by
  intro i
  change ∀ᵐ y ∂(P.law i).map (Model.excessValueMap a), y ≤ H
  exact (ae_map_iff (Model.measurable_excessValueMap a).aemeasurable measurableSet_Iic).mpr
    ((hcap i).mono fun x hx => (Model.excessValueMap_le_self ha x).trans hx)

lemma positiveOfferIntensity_excessOffers (R : Model.Instance m) {a : ℝ} (ha : 0 ≤ a) :
    positiveOfferIntensity (R.excessOffers a) = excessIntensity (positiveOfferIntensity R) a := by
  apply FiniteMeasure.toMeasure_injective
  apply Measure.ext
  intro E hE
  rw [positiveOfferIntensity_toMeasure,Measure.finsetSum_apply]
  change (∑ i, (((R.excessOffers a).law i).restrict (Ioi 0)) E) =
    ((Model.excessLaw (positiveOfferIntensity R : Measure ℝ) a).restrict (Ioi 0)) E
  rw [Measure.restrict_apply hE,Model.excessLaw,
    Measure.map_apply (Model.measurable_excessValueMap a) (hE.inter measurableSet_Ioi),
    positiveOfferIntensity_toMeasure,Measure.finsetSum_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.restrict_apply hE,Model.Instance.excessOffers_law,Model.excessLaw,
    Measure.map_apply (Model.measurable_excessValueMap a) (hE.inter measurableSet_Ioi),
    Measure.restrict_apply ((Model.measurable_excessValueMap a) (hE.inter measurableSet_Ioi))]
  have hsub : (Model.excessValueMap a) ⁻¹' (E ∩ Ioi 0) ⊆ Ioi (0 : ℝ) := by
    intro x hx
    have hp : 0 < Model.excessValueMap a x := hx.2
    exact ha.trans_lt ((Model.excessValueMap_positive_iff ha).mp hp)
  rw [inter_eq_left.mpr hsub]

lemma FiniteIntensityHybridInstance.ext_data (B C : FiniteIntensityHybridInstance n)
    (hcap : B.cap = C.cap) (hterm : B.terminal = C.terminal)
    (hind : B.individuals = C.individuals) (hint : B.intensity = C.intensity) : B = C := by
  cases B
  cases C
  cases hcap
  cases hterm
  cases hind
  cases hint
  rfl

lemma poissonizedFamily_excessState (P : Model.Instance n) (R : Model.Instance m) (H a : ℝ≥0)
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) :
    (poissonizedFamily P R H hP hR).excessState a =
      poissonizedFamily (P.excessOffers a) (R.excessOffers a) H (excessOffers_bounded P a.property hP)
        (excessOffers_bounded R a.property hR) := by
  apply FiniteIntensityHybridInstance.ext_data
  · rfl
  · rfl
  · rfl
  · exact (positiveOfferIntensity_excessOffers R a.property).symm

end ProphetSecretary.Limiting
