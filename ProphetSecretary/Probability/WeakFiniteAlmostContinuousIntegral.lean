import ProphetSecretary.Probability.WeakAlmostContinuousIntegral
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure

/-!
# Bounded almost-continuous integrals under weak finite-measure convergence

A nonzero limit is normalized using the actual library continuity theorem,
then the probability-measure result is multiplied by the converging masses.
At a zero limiting measure, the explicit norm bound by H times the mass proves
convergence directly. No positive limiting mass is assumed in the result.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace ProphetSecretary.Probability
variable {Ω Γ : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] in
lemma finiteMeasure_real_univ_eq_mass (μ : FiniteMeasure Ω) :
    (μ : Measure Ω).real Set.univ = (μ.mass : ℝ) := by
  simpa only [Measure.real,ENNReal.coe_toReal] using
    (congrArg ENNReal.toReal (FiniteMeasure.ennreal_mass (μ := μ))).symm

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] in
lemma finiteMeasure_integral_eq_mass_mul_normalize [Nonempty Ω] (μ : FiniteMeasure Ω) (f : Ω → ℝ) :
    (∫ x, f x ∂(μ : Measure Ω)) = (μ.mass : ℝ) * ∫ x, f x ∂(μ.normalize : Measure Ω) := by
  have heq : (μ : Measure Ω) = μ.mass • (μ.normalize : Measure Ω) :=
    congrArg (fun ν : FiniteMeasure Ω => (ν : Measure Ω)) μ.self_eq_mass_smul_normalize
  rw [heq,integral_smul_nnreal_measure]
  rfl

/-- The finite-measure counterpart of bounded almost-continuous weak integral
transfer, with its zero-limit-mass case proved rather than excluded. -/
theorem finite_integral_tendsto_of_weak_ae_continuous_bounded [Nonempty Ω] [HasOuterApproxClosed Ω]
    {l : Filter Γ} [l.IsCountablyGenerated] {μs : Γ → FiniteMeasure Ω} {μ : FiniteMeasure Ω}
    (hweak : Tendsto μs l (𝓝 μ)) {f : Ω → ℝ} (hf : Measurable f) {H : ℝ}
    (hbound : ∀ x, |f x| ≤ H) (hc : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt f x) :
    Tendsto (fun m => ∫ x, f x ∂(μs m : Measure Ω)) l (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  have hmass : Tendsto (fun m => ((μs m).mass : ℝ)) l (𝓝 (μ.mass : ℝ)) := NNReal.tendsto_coe.2 hweak.mass
  by_cases hzero : μ = 0
  · have hmass₀ : Tendsto (fun m => ((μs m).mass : ℝ)) l (𝓝 (0 : ℝ)) := by simpa only [hzero,FiniteMeasure.zero_mass,NNReal.coe_zero] using hmass
    have hupper : Tendsto (fun m => H * ((μs m).mass : ℝ)) l (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hmass₀.const_mul H
    have hnorm (m : Γ) : ‖∫ x, f x ∂(μs m : Measure Ω)‖ ≤ H * ((μs m).mass : ℝ) := by
      have h := norm_integral_le_of_norm_le_const (μ := (μs m : Measure Ω)) (f := f)
        (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x)
      simpa only [finiteMeasure_real_univ_eq_mass] using h
    have ht := squeeze_zero_norm hnorm hupper
    simpa only [hzero,FiniteMeasure.toMeasure_zero,integral_zero_measure] using ht
  · have hnorm := FiniteMeasure.tendsto_normalize_of_tendsto hweak hzero
    have hcNorm : ∀ᵐ x ∂(μ.normalize : Measure Ω), ContinuousAt f x := by
      rw [μ.toMeasure_normalize_eq_of_nonzero hzero]
      exact Measure.ae_smul_measure hc _
    have hconv := integral_tendsto_of_weak_ae_continuous_bounded hnorm hf hbound hcNorm
    have ht := hmass.mul hconv
    simpa only [← finiteMeasure_integral_eq_mass_mul_normalize] using ht

end ProphetSecretary.Probability
