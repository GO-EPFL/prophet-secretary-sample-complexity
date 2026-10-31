import ProphetSecretary.Probability.SingleMarginalTilt
import ProphetSecretary.Model.MarginalPremium

/-!
# One-marginal transition residuals

The canonical design is fixed while one offer law is tilted. The change of its
positive acceptance premium is an exact affine integral, rather than an
unbiasedness assumption about a random empirical design.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

lemma positivePremium_tiltLaw (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : Integrable id μ) (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ᵐ x ∂μ, |h x| ≤ 1) {θ : ℝ} (hθ : |θ| ≤ 1 / 4) (w v : ℝ) :
    positivePremium (tiltLaw μ h θ) w v = positivePremium μ w v +
      θ * ∫ x, h x * max (w * x - v) 0 ∂μ := by
  have h0 : ∀ᵐ x ∂μ, 0 ≤ tiltFactor h θ x := hb.mono (fun x hx ↦
    (by norm_num : (0 : ℝ) ≤ 3 / 4).trans (tiltFactor_bounds hθ hx).1)
  have hf := integrable_positivePart μ hμ w v
  have hprod : Integrable (fun x ↦ h x * max (w * x - v) 0) μ :=
    hf.bdd_mul hh.aestronglyMeasurable (by simpa only [Real.norm_eq_abs] using hb)
  unfold positivePremium
  rw [integral_tiltLaw hh h0]
  have he : (fun x ↦ tiltFactor h θ x * max (w * x - v) 0) =
      (fun x ↦ max (w * x - v) 0 + θ * (h x * max (w * x - v) 0)) := by
    funext x
    unfold tiltFactor
    ring
  rw [he, integral_add (f := fun x ↦ max (w * x - v) 0)
    (g := fun x ↦ θ * (h x * max (w * x - v) 0)) hf (hprod.const_mul θ), integral_const_mul]

variable {n : ℕ}

lemma Instance.transitionResidual_singleMarginal_same (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (i : Fin n) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂P.law i, |h x| ≤ 1) (hm : ∫ x, h x ∂P.law i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) (w c : ℝ) (u : Fin n → ℝ) :
    P.transitionResidual (P.singleMarginalTilt i h hh hb hm θ hθ) w c u i =
      -θ * ∫ a, h a * max (w * a - P.continuationAtArrival w c (fun _ ↦ 0) u i) 0 ∂P.law i := by
  unfold Instance.transitionResidual Instance.lawResidual
  rw [P.singleMarginalTilt_law_same i h hh hb hm θ hθ,
    positivePremium_tiltLaw (P.law i) (P.integrable_maximum_iff.mp hP i) h hh hb hθ]
  ring

lemma Instance.transitionResidual_singleMarginal_other (P : Instance n) (i : Fin n) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂P.law i, |h x| ≤ 1) (hm : ∫ x, h x ∂P.law i = 0)
    {θ : ℝ} (hθ : |θ| ≤ 1 / 4) (w c : ℝ) (u : Fin n → ℝ) {j : Fin n} (hji : j ≠ i) :
    P.transitionResidual (P.singleMarginalTilt i h hh hb hm θ hθ) w c u j = 0 := by
  unfold Instance.transitionResidual Instance.lawResidual
  rw [P.singleMarginalTilt_law_other i h hh hb hm θ hθ hji, sub_self]

end ProphetSecretary.Model
