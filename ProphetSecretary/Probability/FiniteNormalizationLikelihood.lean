import ProphetSecretary.Probability.FiniteNormalizationScores
import ProphetSecretary.Probability.WideLikelihoodPath
import Mathlib.MeasureTheory.Integral.Lebesgue.Map

/-!
# Positive normalization commutes with actual likelihood laws

The base scale M is fixed, not recomputed under a tilted law. The pushforward
of a tilted marginal has exactly the transformed score h(My). This measure
identity passes coordinatewise to the genuine independent finite family,
including the total wider-parameter path used for uniform regularity.
-/

open MeasureTheory Set
open scoped Classical ENNReal
namespace ProphetSecretary.Probability

lemma tiltLaw_fixedBaseNormalization_map (μ : Measure ℝ) {M : ℝ} (hM : 0<M)
    (h : ℝ → ℝ) (hh : Measurable h) (θ : ℝ) :
    (tiltLaw μ h θ).map (M⁻¹*·)=tiltLaw (μ.map (M⁻¹*·)) (fun y => h (M*y)) θ := by
  ext s hs
  rw [Measure.map_apply (ProphetSecretary.Model.measurable_valueScale M⁻¹) hs]
  unfold tiltLaw
  rw [withDensity_apply _ ((ProphetSecretary.Model.measurable_valueScale M⁻¹) hs),
    withDensity_apply _ hs,
    Measure.restrict_map (ProphetSecretary.Model.measurable_valueScale M⁻¹) hs]
  have hF : Measurable (fun y : ℝ => ENNReal.ofReal (tiltFactor (fun y => h (M*y)) θ y)) :=
    ENNReal.measurable_ofReal.comp (measurable_tiltFactor (hh.comp (ProphetSecretary.Model.measurable_valueScale M)) θ)
  rw [lintegral_map hF (ProphetSecretary.Model.measurable_valueScale M⁻¹)]
  apply lintegral_congr_ae
  exact Filter.Eventually.of_forall (fun x => by
    change ENNReal.ofReal (1+θ*h x)=ENNReal.ofReal (1+θ*h (M*(M⁻¹*x)))
    rw [←mul_assoc,mul_inv_cancel₀ hM.ne',one_mul])

end ProphetSecretary.Probability

namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma Instance.fixedBaseNormalizedScore_bounded_ae (P : Instance n) {M : ℝ} (hM : 0<M)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x|≤1) :
    ∀ i, ∀ᵐ y ∂(P.scale M⁻¹ (inv_nonneg.mpr hM.le)).law i, |fixedBaseNormalizedScore M h i y|≤1 := by
  intro i
  have hSet : MeasurableSet {y : ℝ | |fixedBaseNormalizedScore M h i y|≤1} := by
    simpa only [Real.norm_eq_abs] using measurableSet_le
      (fixedBaseNormalizedScore_measurable M hh i).norm measurable_const
  apply (ae_map_iff (measurable_valueScale M⁻¹).aemeasurable hSet).mpr
  filter_upwards [hb i] with x hx
  change |h i (M*(M⁻¹*x))|≤1
  rwa [←mul_assoc,mul_inv_cancel₀ hM.ne',one_mul]

/-- Equality of the actual law family, with the base benchmark held fixed for
all parameters. It also applies directly after reversing the parameter. -/
theorem Instance.fixedBaseNormalization_likelihoodWidePath (P : Instance n) {M : ℝ} (hM : 0<M)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x|≤1) (hm : ∀ i, ∫ x, h i x ∂P.law i=0) (θ : ℝ) :
    (P.scale M⁻¹ (inv_nonneg.mpr hM.le)).likelihoodWidePath (fixedBaseNormalizedScore M h)
      (fixedBaseNormalizedScore_measurable M hh) (P.fixedBaseNormalizedScore_bounded_ae hM h hh hb)
      (P.fixedBaseNormalizedScore_centered hM h hh hm) θ=
      (P.likelihoodWidePath h hh hb hm θ).scale M⁻¹ (inv_nonneg.mpr hM.le) := by
  apply Instance.ext_law
  funext i
  change tiltLaw ((P.law i).map (M⁻¹*·)) (fun y => h i (M*y)) (halfParameter θ)=
    (tiltLaw (P.law i) (h i) (halfParameter θ)).map (M⁻¹*·)
  exact (tiltLaw_fixedBaseNormalization_map (P.law i) hM (h i) (hh i) (halfParameter θ)).symm

end ProphetSecretary.Model
