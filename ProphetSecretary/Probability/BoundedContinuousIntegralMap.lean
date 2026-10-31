import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Integration as a continuous linear map on bounded continuous functions

This packages the library integral bound for exchanging a norm-summable
series of continuous test functions with a finite aggregate of offer laws.
-/
open MeasureTheory BoundedContinuousFunction
namespace ProphetSecretary.Probability
noncomputable def probabilityIntegralCLM (p : ProbabilityMeasure ℝ) : (ℝ →ᵇ ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun f => ∫ x, f x ∂(p : Measure ℝ)
      map_add' := fun f g => integral_add (f.integrable _) (g.integrable _)
      map_smul' := fun c f => by
        change (∫ x, c * f x ∂(p : Measure ℝ)) = c * (∫ x, f x ∂(p : Measure ℝ))
        exact integral_const_mul c f }
    1 (fun f => by simpa using f.norm_integral_le_norm (p : Measure ℝ))
lemma probabilityIntegralCLM_apply (p : ProbabilityMeasure ℝ) (f : ℝ →ᵇ ℝ) :
    probabilityIntegralCLM p f = ∫ x, f x ∂(p : Measure ℝ) := rfl
end ProphetSecretary.Probability
