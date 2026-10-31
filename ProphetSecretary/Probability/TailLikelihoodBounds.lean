import ProphetSecretary.Probability.QuarterLikelihoodBounds

/-!
# Uniform positive-tail bounds under bounded marginal likelihood tilts

The factor 5/4 is independent of the number of variables. The bound applies
to arbitrary measurable tail events, without a total-first-moment assumption.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Probability

lemma tiltLaw_real_le_quarter {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (h : Ω → ℝ)
    (hb : ∀ᵐ x ∂μ, |h x|≤1) {θ : ℝ} (hθ : |θ|≤1/4) (S : Set Ω) :
    (tiltLaw μ h θ).real S≤(5/4)*μ.real S := by
  have hDom : tiltLaw μ h θ≤ENNReal.ofReal (5/4) • μ := by
    rw [tiltLaw,←withDensity_const]
    exact withDensity_mono (hb.mono (fun x hx => ENNReal.ofReal_le_ofReal (tiltFactor_bounds hθ hx).2))
  have hFinite : (ENNReal.ofReal (5/4) • μ) S≠⊤ := by
    rw [Measure.smul_apply,smul_eq_mul]
    exact ENNReal.mul_ne_top (by simp) (measure_ne_top μ S)
  have hReal := ENNReal.toReal_mono hFinite (hDom S)
  simpa only [←measureReal_def,measureReal_ennreal_smul_apply,ENNReal.toReal_ofReal (by norm_num : (0:ℝ)≤5/4)] using hReal

end ProphetSecretary.Probability

namespace ProphetSecretary.Model.Instance
open ProphetSecretary.Probability

lemma tailCount_likelihoodWidePath_quarter_le {n : ℕ} (P : Instance n)
    (score : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (score i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |score i x|≤1)
    (hm : ∀ i, (∫ x, score i x ∂P.law i)=0) {θ : ℝ} (hθ : |θ|≤1/4) (b : ℝ) :
    (P.likelihoodWidePath score hh hb hm θ).tailCount b≤(5/4)*P.tailCount b := by
  unfold tailCount
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  rw [P.likelihoodWidePath_law_quarter score hh hb hm hθ i]
  exact tiltLaw_real_le_quarter (P.law i) (score i) (hb i) hθ (Ioi b)

end ProphetSecretary.Model.Instance
