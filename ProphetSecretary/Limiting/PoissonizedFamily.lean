import ProphetSecretary.Limiting.PositiveOfferIntensity
import ProphetSecretary.Limiting.FiniteBernoulliApproximation

/-!
# Replacing a finite independent offer family by its positive Poisson intensity

The retained individual laws are unchanged. The positive restrictions of the
replaced laws form the actual finite mark intensity, with terminal reward zero.
The construction includes arbitrary atoms and zero-maximum auxiliary instances.
-/

open MeasureTheory Set
open scoped NNReal

namespace ProphetSecretary.Limiting

variable {n m : ℕ}

noncomputable def poissonizedFamily (P : Model.Instance n) (R : Model.Instance m) (H : ℝ≥0)
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) : FiniteIntensityHybridInstance n where
  cap := H
  terminal := 0
  terminal_le_cap := by positivity
  individuals := P
  individual_bounded := hP
  intensity := positiveOfferIntensity R
  intensity_supported := positiveOfferIntensity_supported R hR

lemma poissonizedFamily_mark_nonnegative (P : Model.Instance n) (R : Model.Instance m) (H : ℝ≥0)
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) (hμ : positiveOfferIntensity R ≠ 0) :
    ∀ᵐ x ∂((positiveOfferIntensity R).normalize : Measure ℝ), 0 ≤ x :=
  (poissonizedFamily P R H hP hR).normalizedMark_nonnegative hμ

lemma poissonizedFamily_mark_integrable (P : Model.Instance n) (R : Model.Instance m) (H : ℝ≥0)
    (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) (hμ : positiveOfferIntensity R ≠ 0) :
    Integrable id ((positiveOfferIntensity R).normalize : Measure ℝ) :=
  (poissonizedFamily P R H hP hR).normalizedMark_integrable hμ

end ProphetSecretary.Limiting
