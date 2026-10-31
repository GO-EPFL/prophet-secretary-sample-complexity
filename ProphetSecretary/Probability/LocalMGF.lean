import ProphetSecretary.Analysis.LocalExpQuadratic
import Mathlib.Probability.Moments.Basic

/-!
# Local moment-generating functions retaining the actual second moment

The Laplace parameter is restricted by |tX|≤1. Centering removes the linear
term, and the remaining bound scales with E[X²], which may be small.
-/

open MeasureTheory ProbabilityTheory Set Filter

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

lemma integrable_exp_mul_of_small {X : Ω → ℝ} (hX : Measurable X) {t : ℝ}
    (hSmall : ∀ᵐ ω ∂μ, |t*X ω| ≤ 1) : Integrable (fun ω => Real.exp (t*X ω)) μ := by
  have hm : Measurable (fun ω => Real.exp (t*X ω)) := (hX.const_mul t).exp
  apply Integrable.of_bound hm.aestronglyMeasurable (Real.exp 1)
  filter_upwards [hSmall] with ω hω
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  exact Real.exp_le_exp.mpr ((le_abs_self _).trans hω)

theorem mgf_le_exp_secondMoment_of_small {X : Ω → ℝ} (hX : Measurable X)
    (hXI : Integrable X μ) (hX2 : Integrable (fun ω => X ω^2) μ)
    (hMean : (∫ ω, X ω ∂μ) = 0) {t : ℝ} (hSmall : ∀ᵐ ω ∂μ, |t*X ω| ≤ 1) :
    mgf X μ t ≤ Real.exp (t^2*(∫ ω, X ω^2 ∂μ)) := by
  have hFirst : Integrable (fun ω => 1+t*X ω) μ := (integrable_const 1).add (hXI.const_mul t)
  have hRhs : Integrable (fun ω => 1+t*X ω+t^2*X ω^2) μ := hFirst.add (hX2.const_mul (t^2))
  have hBound : ∀ᵐ ω ∂μ, Real.exp (t*X ω) ≤ 1+t*X ω+t^2*X ω^2 := by
    filter_upwards [hSmall] with ω hω
    simpa only [mul_pow] using ProphetSecretary.Analysis.exp_le_one_add_add_sq hω
  have hInt : (∫ ω, (1+t*X ω+t^2*X ω^2) ∂μ) = 1+t^2*(∫ ω, X ω^2 ∂μ) := by
    rw [integral_add hFirst (hX2.const_mul (t^2)),
      integral_add (integrable_const 1) (hXI.const_mul t),integral_const_mul,integral_const_mul,hMean]
    simp
  calc
    mgf X μ t ≤ ∫ ω, (1+t*X ω+t^2*X ω^2) ∂μ :=
      integral_mono_ae (integrable_exp_mul_of_small hX hSmall) hRhs hBound
    _ = 1+t^2*(∫ ω, X ω^2 ∂μ) := hInt
    _ ≤ _ := by simpa only [add_comm] using Real.add_one_le_exp (t^2*(∫ ω, X ω^2 ∂μ))

end ProphetSecretary.Probability
