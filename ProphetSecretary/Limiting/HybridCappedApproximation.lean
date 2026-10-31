import ProphetSecretary.Limiting.HybridCappingWeak
import ProphetSecretary.Limiting.HybridCappedDesignError

/-!
# Capped Bernoulli values with moving cap and duration coefficient

The finite rare-design error is uniform in both choices. Its vanishing is
combined with the actual weak value limit of the capped hybrid instances.
Only optimized values are passed to the limit.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical
namespace ProphetSecretary.Limiting.FiniteIntensityHybridInstance
variable {n : ℕ}

lemma cappedBernoulliApproximation_value_tendsto (B : FiniteIntensityHybridInstance n)
    (hZero : B.terminal=0) (hμ : B.intensity≠0)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hKs : ∀ m, 0<Ks m) (hK : 0<K)
    (hKLimit : Tendsto Ks atTop (𝓝 K)) {cs : ℕ → ℝ} {c w : ℝ}
    (hcs : ∀ m, 0≤cs m) (hw : 0<w) (hcLimit : Tendsto cs atTop (𝓝 c)) :
    Tendsto (fun m => Model.optimalScalarValue ((B.bernoulliApproximation hμ m).cap (Ks m)) w (cs m)) atTop
      (𝓝 ((B.capAt K hK).optimalScalarValue w c)) := by
  let rate := (B.intensity : Measure ℝ).real univ
  let k := fun m => bernoulliMultiplicity rate m
  let p := fun m => bernoulliProbability rate measureReal_nonneg m
  let err := fun m => (k m:ℝ)*(w*(p m:ℝ)^2*(B.cap:ℝ))+
    (Real.pi/2)*w*(B.cap:ℝ)*Real.sqrt ((k m:ℝ)*(p m:ℝ)^2)
  have hErr : Tendsto err atTop (𝓝 (0:ℝ)) := bernoulliProbability_error_tendsto_zero rate measureReal_nonneg w B.cap
  have hBound (m : ℕ) :
      |Model.optimalScalarValue ((B.bernoulliApproximation hμ m).cap (Ks m)) w (cs m)-
        (B.capAt (Ks m) (hKs m)).optimalScalarValue w (cs m)|≤err m := by
    have h := B.cappedBernoulliDesign_value_error hZero hμ (Ks m) (hKs m) (p m)
      (bernoulliProbability_total rate measureReal_nonneg m).symm hw (hcs m)
    apply h.trans_eq
    dsimp only [err,k,p]
    ring
  have hDiff : Tendsto (fun m => Model.optimalScalarValue ((B.bernoulliApproximation hμ m).cap (Ks m)) w (cs m)-
      (B.capAt (Ks m) (hKs m)).optimalScalarValue w (cs m)) atTop (𝓝 (0:ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hErr
    intro m
    simpa only [sub_zero,Real.norm_eq_abs] using hBound m
  have hValue := B.capAt_value_tendsto_moving_duration hKs hK hKLimit hcs hw.le hcLimit
  simpa only [sub_add_cancel,zero_add] using hDiff.add hValue

end ProphetSecretary.Limiting.FiniteIntensityHybridInstance
