import ProphetSecretary.Limiting.HybridCappedApproximation
import ProphetSecretary.Limiting.HybridDesignCapExcess
import ProphetSecretary.Reach.Clipping

/-!
# Reward-only clipping for a finite-intensity hybrid instance

The finite clipping inequality is applied before the Bernoulli multiplicity
limit. Cap heights converge to the actual hybrid reward value; aggregate excess
is exact in every design and continuous at moving caps, including atoms. The
zero-intensity case uses the exact finite-instance identity.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical
namespace ProphetSecretary.Limiting.FiniteIntensityHybridInstance
variable {n : ℕ}

lemma reward_clipping_value_le_nonzero (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    (hμ : B.intensity≠0) (hV : 0<B.optimalScalarValue 1 0) :
    let K : ℝ≥0 := ⟨B.optimalScalarValue 1 0,hV.le⟩
    (B.capAt K hV).optimalScalarValue 1 (B.totalCapExcess K)≤B.optimalScalarValue 1 0 := by
  let K : ℝ≥0 := ⟨B.optimalScalarValue 1 0,hV.le⟩
  have hK : 0<K := hV
  let Q := B.bernoulliApproximation hμ
  have hQI (m : ℕ) : Integrable Model.Instance.maximum (Q m).valuesLaw :=
    finitePoissonDesign_integrable_maximum B.individuals (B.intensity.normalize : Measure ℝ)
      (B.normalizedMark_nonnegative hμ) _ _
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) (B.normalizedMark_integrable hμ)
  let hs := fun m => (Q m).clippingHeight 1 0
  have hHeight (m : ℕ) : (hs m:ℝ)=Model.optimalScalarValue (Q m) 1 0 := by
    simpa only [div_one] using (Q m).clippingHeight_coe (hQI m) zero_lt_one le_rfl
  have hVLim := B.bernoulliApproximation_value_tendsto hZero hμ zero_lt_one le_rfl
  have hHeightLim : Tendsto hs atTop (𝓝 K) := by
    apply NNReal.tendsto_coe.1
    have hFun : (fun m => (hs m:ℝ))=(fun m => Model.optimalScalarValue (Q m) 1 0) := funext hHeight
    rw [hFun]
    exact hVLim
  let Ks := fun m => max (hs m) (K/2)
  have hKs (m : ℕ) : 0<Ks m := (half_pos hK).trans_le (le_max_right _ _)
  have hHalfLe : K/2≤K := (half_lt_self hK).le
  have hKsLim : Tendsto Ks atTop (𝓝 K) := by
    simpa only [max_eq_left hHalfLe] using hHeightLim.max (tendsto_const_nhds : Tendsto (fun _ : ℕ => K/2) atTop (𝓝 (K/2)))
  have hSame : ∀ᶠ m in atTop, Ks m=hs m := by
    filter_upwards [hHeightLim.eventually (Ioi_mem_nhds (half_lt_self hK))] with m hm
    exact max_eq_left hm.le
  have hELim := B.totalCapExcess_tendsto hKsLim
  have hCapped := B.cappedBernoulliApproximation_value_tendsto hZero hμ hKs hK hKsLim
    (fun m => B.totalCapExcess_nonnegative (Ks m)) zero_lt_one hELim
  have hClip : ∀ᶠ m in atTop,
      Model.optimalScalarValue ((Q m).cap (Ks m)) 1 (B.totalCapExcess (Ks m))≤Model.optimalScalarValue (Q m) 1 0 := by
    filter_upwards [hSame] with m hm
    rw [hm]
    have h := (Q m).clippedValue_le (hQI m) zero_lt_one le_rfl
    simp only [Model.Instance.clippedDurationCoefficient,zero_add,one_mul] at h
    change Model.optimalScalarValue ((Q m).cap (hs m)) 1 ((Q m).tailSum (hs m))≤Model.optimalScalarValue (Q m) 1 0 at h
    have hTail := B.bernoulliApproximation_tailSum hμ m (hs m)
    rwa [hTail] at h
  exact le_of_tendsto_of_tendsto hCapped hVLim hClip

/-- The actual hybrid version of the clipping inequality used at the reward
boundary. Its premise is positivity of the actual optimized reward value. -/
theorem reward_clipping_value_le (B : FiniteIntensityHybridInstance n) (hZero : B.terminal=0)
    (hV : 0<B.optimalScalarValue 1 0) :
    let K : ℝ≥0 := ⟨B.optimalScalarValue 1 0,hV.le⟩
    (B.capAt K hV).optimalScalarValue 1 (B.totalCapExcess K)≤B.optimalScalarValue 1 0 := by
  by_cases hμ : B.intensity=0
  · let K : ℝ≥0 := ⟨B.optimalScalarValue 1 0,hV.le⟩
    have hK : 0<K := hV
    have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
    have hBase := B.value_zero_intensity hZero hμ zero_le_one le_rfl
    have hHeight : B.individuals.clippingHeight 1 0=K := by
      apply NNReal.eq
      rw [B.individuals.clippingHeight_coe hP zero_lt_one le_rfl,div_one]
      exact hBase.symm
    have hExcess : B.totalCapExcess K=B.individuals.tailSum K := by
      simp only [totalCapExcess,poissonCapExcess,hμ,FiniteMeasure.toMeasure_zero,integral_zero_measure,add_zero,
        individualCapExcess,Model.Instance.tailSum]
    have hDμ : (B.capAt K hK).intensity=0 := by
      change B.intensity.map (Model.capValue K)=0
      rw [hμ]
      apply FiniteMeasure.toMeasure_injective
      change (0 : Measure ℝ).map (Model.capValue K)=0
      exact Measure.map_zero _
    have hTarget := (B.capAt K hK).value_zero_intensity hZero hDμ zero_le_one (B.totalCapExcess_nonnegative K)
    change (B.capAt K hK).optimalScalarValue 1 (B.totalCapExcess K)≤B.optimalScalarValue 1 0
    rw [hTarget,hExcess,hBase]
    have h := B.individuals.clippedValue_le hP zero_lt_one le_rfl
    rw [hHeight] at h
    simpa only [capAt,Model.Instance.clippedDurationCoefficient,zero_add,one_mul] using h
  · exact B.reward_clipping_value_le_nonzero hZero hμ hV

end ProphetSecretary.Limiting.FiniteIntensityHybridInstance
