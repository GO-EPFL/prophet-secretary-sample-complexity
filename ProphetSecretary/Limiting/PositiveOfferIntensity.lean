import ProphetSecretary.Limiting.BernoulliValueComparison
import ProphetSecretary.Model.PositivePremiumTail

/-!
# The positive-offer intensity of a finite independent family

Each marginal contributes its actual restriction to positive values. Their
finite sum is the Poisson mark intensity in `lem:causal-poisson`. Its total
mass is exactly the expected positive-offer count, and integrating a positive
premium agrees with the corresponding sum of original marginal premia.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

noncomputable def positiveOfferMarginal (P : Model.Instance n) (i : Fin n) : FiniteMeasure ℝ :=
  ⟨(P.law i).restrict (Ioi 0), inferInstance⟩

noncomputable def positiveOfferIntensity (P : Model.Instance n) : FiniteMeasure ℝ :=
  ∑ i, positiveOfferMarginal P i

lemma positiveOfferIntensity_toMeasure (P : Model.Instance n) :
    (positiveOfferIntensity P : Measure ℝ) = ∑ i, (P.law i).restrict (Ioi 0) := by
  unfold positiveOfferIntensity
  rw [FiniteMeasure.toMeasure_sum]
  rfl

lemma positiveOfferIntensity_mass (P : Model.Instance n) :
    (positiveOfferIntensity P : Measure ℝ).real univ = P.positiveCount := by
  unfold Measure.real
  rw [positiveOfferIntensity_toMeasure, Measure.finsetSum_apply,
    ENNReal.toReal_sum (fun i _ => measure_ne_top ((P.law i).restrict (Ioi 0)) univ)]
  simp only [Measure.restrict_apply_univ]
  rfl

lemma positiveOfferIntensity_supported (P : Model.Instance n) {H : ℝ}
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ᵐ x ∂(positiveOfferIntensity P : Measure ℝ), x ∈ Ioc (0 : ℝ) H := by
  rw [positiveOfferIntensity_toMeasure, ae_finsetSum_measure_iff]
  intro i _
  filter_upwards [ae_restrict_mem measurableSet_Ioi, ae_restrict_of_ae (hcap i)] with x hx hH
  exact ⟨hx,hH⟩

lemma positivePremium_eq_positiveRestriction (κ : Measure ℝ) (w v : ℝ) (hw : 0 ≤ w) (hv : 0 ≤ v) :
    Model.positivePremium κ w v = ∫ x, max (w * x - v) 0 ∂κ.restrict (Ioi 0) := by
  rw [← integral_indicator measurableSet_Ioi]
  unfold Model.positivePremium
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    by_cases hx : x ∈ Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hx]
    · rw [Set.indicator_of_notMem hx]
      have hxn : x ≤ 0 := not_lt.mp hx
      exact max_eq_right (sub_nonpos.mpr ((mul_nonpos_of_nonneg_of_nonpos hw hxn).trans hv))

lemma positiveOfferIntensity_premium_sum (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {w v : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v) :
    (∫ x, max (w * x - v) 0 ∂(positiveOfferIntensity P : Measure ℝ)) =
      ∑ i, Model.positivePremium (P.law i) w v := by
  rw [positiveOfferIntensity_toMeasure, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i _
    exact (positivePremium_eq_positiveRestriction (P.law i) w v hw hv).symm
  · intro i _
    exact (Model.integrable_positivePart (P.law i) (P.integrable_maximum_iff.mp hP i) w v).integrableOn

lemma finiteMeasure_integral_normalize (μ : FiniteMeasure ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(μ : Measure ℝ)) = (μ : Measure ℝ).real univ * ∫ x, f x ∂(μ.normalize : Measure ℝ) := by
  have he := congrArg FiniteMeasure.toMeasure μ.self_eq_mass_smul_normalize
  simp only [FiniteMeasure.toMeasure_smul] at he
  have he' : (μ : Measure ℝ) = μ.mass • (μ.normalize : Measure ℝ) := he
  nth_rw 1 [he']
  rw [integral_smul_nnreal_measure]
  change (μ.mass : ℝ) * (∫ x, f x ∂(μ.normalize : Measure ℝ)) =
    (μ : Measure ℝ).real univ * (∫ x, f x ∂(μ.normalize : Measure ℝ))
  rfl

/-- The positive intensity's normalized mark law has exactly the original
sum of positive premia after multiplication by the total intensity. -/
lemma positiveOfferIntensity_normalized_premium (P : Model.Instance n)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) {w v : ℝ} (hw : 0 ≤ w) (hv : 0 ≤ v) :
    (positiveOfferIntensity P : Measure ℝ).real univ *
      Model.positivePremium (positiveOfferIntensity P).normalize w v =
        ∑ i, Model.positivePremium (P.law i) w v := by
  rw [← positiveOfferIntensity_premium_sum P hP hw hv, finiteMeasure_integral_normalize]
  rfl

end ProphetSecretary.Limiting
