import ProphetSecretary.Probability.WideLikelihoodTilt
import ProphetSecretary.Model.MarginalGradient

/-!
# Local re-centering of the product likelihood family

At a base parameter in the wider half interval, half of the current likelihood
score is centered and bounded by one. Tilting it by twice the displacement
reproduces the original law at the displaced parameter exactly.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

noncomputable def recenteredUnitScore (h : ℝ → ℝ) (θ x : ℝ) : ℝ := (1 / 2) * tiltedScore h θ x

lemma measurable_recenteredUnitScore {h : ℝ → ℝ} (hh : Measurable h) (θ : ℝ) :
    Measurable (recenteredUnitScore h θ) := measurable_const.mul (measurable_tiltedScore hh θ)

lemma recenteredUnitScore_bound {μ : Measure ℝ} {h : ℝ → ℝ}
    (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1 / 2) :
    ∀ᵐ x ∂tiltLaw μ h θ, |recenteredUnitScore h θ x| ≤ 1 := by
  apply (tiltLaw_absolutelyContinuous μ h θ).ae_le
  filter_upwards [hb] with x hx
  have hs := tiltedScore_half_abs_le hθ hx
  unfold recenteredUnitScore tiltedScore tiltFactor
  rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  nlinarith

lemma recenteredUnitScore_centered {μ : Measure ℝ} {h : ℝ → ℝ}
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) (hm : ∫ x, h x ∂μ = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 2) : ∫ x, recenteredUnitScore h θ x ∂tiltLaw μ h θ = 0 := by
  unfold recenteredUnitScore
  rw [integral_const_mul, tiltedScore_half_centered hh hb hm hθ, mul_zero]

lemma tiltLaw_recenteredUnitScore {μ : Measure ℝ} {h : ℝ → ℝ}
    (hh : Measurable h) (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1 / 2) (δ : ℝ) :
    tiltLaw (tiltLaw μ h θ) (recenteredUnitScore h θ) (2 * δ) = tiltLaw μ h (θ + δ) := by
  unfold tiltLaw
  rw [← withDensity_mul μ ((measurable_tiltFactor hh θ).ennreal_ofReal)
    ((measurable_tiltFactor (measurable_recenteredUnitScore hh θ) (2 * δ)).ennreal_ofReal)]
  apply withDensity_congr_ae
  filter_upwards [hb] with x hx
  have hp : 0 < tiltFactor h θ x := by
    have hlow := (tiltFactor_half_bounds hθ hx).1
    change 0 < 1 + θ * h x
    linarith
  change ENNReal.ofReal (tiltFactor h θ x) * ENNReal.ofReal (tiltFactor (recenteredUnitScore h θ) (2 * δ) x) = _
  rw [← ENNReal.ofReal_mul hp.le]
  congr 1
  unfold recenteredUnitScore tiltedScore tiltFactor
  change 0 < 1 + θ * h x at hp
  field_simp [hp.ne']
  ring

end ProphetSecretary.Probability

namespace ProphetSecretary.Model.Instance

open ProphetSecretary.Probability

variable {n : ℕ}

lemma likelihoodWideTilt_rebase (P : Instance n) (h : Fin n → ℝ → ℝ)
    (hh : ∀ i, Measurable (h i)) (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x| ≤ 1)
    (hm : ∀ i, ∫ x, h i x ∂P.law i = 0) {θ δ : ℝ}
    (hθ : |θ| ≤ 1 / 2) (hδ : |2 * δ| ≤ 1 / 4) (hθδ : |θ + δ| ≤ 1 / 2) :
    (P.likelihoodWideTilt h hh hb hm θ hθ).likelihoodTilt
      (fun i ↦ recenteredUnitScore (h i) θ)
      (fun i ↦ measurable_recenteredUnitScore (hh i) θ)
      (fun i ↦ recenteredUnitScore_bound (hb i) hθ)
      (fun i ↦ recenteredUnitScore_centered (hh i) (hb i) (hm i) hθ) (2 * δ) hδ =
        P.likelihoodWideTilt h hh hb hm (θ + δ) hθδ := by
  apply Instance.ext_law
  funext i
  exact tiltLaw_recenteredUnitScore (hh i) (hb i) hθ δ

end ProphetSecretary.Model.Instance
