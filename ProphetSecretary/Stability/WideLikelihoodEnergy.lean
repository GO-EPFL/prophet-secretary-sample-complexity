import ProphetSecretary.Stability.WideLikelihoodEnvelope
import ProphetSecretary.Probability.WideInformation

/-!
# Envelope energy throughout the likelihood neighborhood

The derivative uses the current centered likelihood score at each actual base
law. Its information is controlled by the original score information uniformly
on a neighborhood containing the manuscript's entire quarter interval.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.optimalScalarValue_likelihoodWidePath_gradient_energy (P : Instance n)
    {w c H : ℝ} (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    let Q := P.likelihoodWideTilt h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWideTilt_bounded h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩) hbound)
    (deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ) ^ 2 ≤
      2 * w ^ 2 * H * (Q.valuePolicy hQ hw.le hc.le).expectedDuration Q *
        (Q.valuePolicy hQ hw.le hc.le).expectedReward Q * information Q.law (fun i ↦ tiltedScore (h i) θ) := by
  dsimp only
  rw [(P.hasDerivAt_optimalScalarValue_likelihoodWidePath hw hc hH hbound h hh hb hm hθ).deriv]
  exact (P.likelihoodWideTilt h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)).marginalPremium_direction_energy
    ((P.likelihoodWideTilt h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)).integrable_maximum_of_bounded
      (P.likelihoodWideTilt_bounded h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩) hbound))
    hw hc.le hH (P.likelihoodWideTilt_bounded h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩) hbound)
    (fun i ↦ tiltedScore (h i) θ) (P.likelihoodWideTilt_score_memLp_two h hh hb hm (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩))

/-- Uniform base-information version, with an explicit factor four on the wider
half neighborhood. All constants are independent of the number of offers. -/
theorem Instance.optimalScalarValue_likelihoodWidePath_gradient_energy_base (P : Instance n)
    {w c H : ℝ} (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) :
    let Q := P.likelihoodWideTilt h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWideTilt_bounded h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩) hbound)
    (deriv (fun t ↦ optimalScalarValue (P.likelihoodWidePath h hh hb hm t) w c) θ) ^ 2 ≤
      4 * w ^ 2 * H * (Q.valuePolicy hQ hw.le hc.le).expectedDuration Q *
        (Q.valuePolicy hQ hw.le hc.le).expectedReward Q * information P.law h := by
  let Q := P.likelihoodWideTilt h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)
  have hQB := P.likelihoodWideTilt_bounded h hh hb hm θ (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩) hbound
  let C := Q.valuePolicy (Q.integrable_maximum_of_bounded hQB) hw.le hc.le
  have hT := C.expectedDuration_nonnegative Q
  have hR := C.expectedReward_nonnegative Q
  have hCoef : 0 ≤ 2 * w ^ 2 * H * C.expectedDuration Q * C.expectedReward Q := by positivity
  have hE := P.optimalScalarValue_likelihoodWidePath_gradient_energy hw hc hH hbound h hh hb hm hθ
  have hI := P.information_likelihoodWideTilt_tiltedScore_le h hh hb hm (abs_le.mpr ⟨hθ.1.le, hθ.2.le⟩)
  apply hE.trans
  have h := mul_le_mul_of_nonneg_left hI hCoef
  convert h using 1
  ring

end ProphetSecretary.Model
