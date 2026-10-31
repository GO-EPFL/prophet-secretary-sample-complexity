import ProphetSecretary.Limiting.CountablePoissonPayloadEnvelope
import ProphetSecretary.Limiting.HybridCanonicalCenteredCoefficient

/-!
# Centered Poisson occurrence tags have zero optimized derivative

Independent centered amplitudes have zero fixed canonical coefficient at
every finite truncation. Their actual countable value therefore has zero
first derivative even when the original anonymous intensity is infinite.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {T : Type} [MeasurableSpace T] [StandardBorelSpace T]

theorem hasDerivAt_optimalScalarValue_centeredPoissonPayload (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b : ℝ} (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) (A : ℝ × T → ℝ) (hA : Measurable A)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0)
    (hCentered : ∀ x, (∫ t, A (x,t) ∂κ)=0) :
    HasDerivAt (fun θ => (B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c)
      0 0 := by
  obtain ⟨ds,_hAnti,hDs,hDsLim⟩ :=
    (dense_univ : Dense (univ : Set ℝ)).exists_seq_strictAnti_tendsto_of_lt (half_pos hb)
  have hPositive (m : ℕ) : 0<ds m := (hDs m).1.1
  have hSmall (m : ℕ) : ds m<b/2 := (hDs m).1.2
  have hCoefficient : Tendsto (fun m => canonicalChronologicalAmplitudeMean
      (B.truncation m (ds m) (by simpa only [hZero,NNReal.coe_zero] using hPositive m)) κ A w c)
      atTop (𝓝 (0 : ℝ)) := by
    simp_rw [canonicalChronologicalAmplitudeMean_centered _ κ A hA hw.le hc.le hD hBound hCentered]
    exact tendsto_const_nhds
  simpa only [mul_zero] using B.hasDerivAt_poissonPayloadValuePath_of_coefficient_limit hZero hw hc hD hb
    κ t0 A hA hBound hVanish id ds hPositive hSmall tendsto_id hDsLim 0 hCoefficient

end ProphetSecretary.Limiting.CountableInstance
