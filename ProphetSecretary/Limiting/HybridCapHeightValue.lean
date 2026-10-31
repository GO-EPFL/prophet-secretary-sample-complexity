import ProphetSecretary.Limiting.HybridCappedApproximation
import ProphetSecretary.Model.CapHeightValue

/-!
# A uniform cap-height value bound for finite-intensity hybrid instances

The finite deterministic transport bound is independent of the number of
virtual Bernoulli identities. Passing their actual value limits gives the
same reward-weight times cap-displacement bound in the hybrid model.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical
namespace ProphetSecretary.Limiting.FiniteIntensityHybridInstance
variable {n : ℕ}

lemma capAt_value_abs_sub_le (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    (K H : ℝ≥0) (hK : 0<K) (hH : 0<H) {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    |(B.capAt K hK).optimalScalarValue w c-(B.capAt H hH).optimalScalarValue w c|≤w*|(K:ℝ)-(H:ℝ)| := by
  by_cases hμ : B.intensity=0
  · have hKμ : (B.capAt K hK).intensity=0 := by
      apply FiniteMeasure.toMeasure_injective
      change (B.intensity : Measure ℝ).map (Model.capValue K)=0
      rw [hμ,FiniteMeasure.toMeasure_zero,Measure.map_zero]
    have hHμ : (B.capAt H hH).intensity=0 := by
      apply FiniteMeasure.toMeasure_injective
      change (B.intensity : Measure ℝ).map (Model.capValue H)=0
      rw [hμ,FiniteMeasure.toMeasure_zero,Measure.map_zero]
    rw [(B.capAt K hK).value_zero_intensity hZero hKμ hw.le hc,
      (B.capAt H hH).value_zero_intensity hZero hHμ hw.le hc]
    exact B.individuals.capHeight_value_abs_sub_le
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) K H hw.le hc
  · have hQI (m : ℕ) : Integrable Model.Instance.maximum (B.bernoulliApproximation hμ m).valuesLaw :=
      finitePoissonDesign_integrable_maximum B.individuals (B.intensity.normalize : Measure ℝ)
        (B.normalizedMark_nonnegative hμ) _ _
        (B.individuals.integrable_maximum_of_bounded B.individual_bounded) (B.normalizedMark_integrable hμ)
    have hKL := B.cappedBernoulliApproximation_value_tendsto hZero hμ (fun _ => hK) hK tendsto_const_nhds
      (fun _ => hc) hw tendsto_const_nhds
    have hHL := B.cappedBernoulliApproximation_value_tendsto hZero hμ (fun _ => hH) hH tendsto_const_nhds
      (fun _ => hc) hw tendsto_const_nhds
    apply le_of_tendsto_of_tendsto (hKL.sub hHL).abs tendsto_const_nhds
    exact Eventually.of_forall fun m => (B.bernoulliApproximation hμ m).capHeight_value_abs_sub_le (hQI m) K H hw.le hc

end ProphetSecretary.Limiting.FiniteIntensityHybridInstance
