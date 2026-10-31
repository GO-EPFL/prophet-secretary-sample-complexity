import ProphetSecretary.Limiting.HybridCapping
import ProphetSecretary.Probability.WeakMovingCap

/-!
# Actual finite-hybrid values at moving cap heights

The fixed original laws are pushed forward by continuous minimum maps. Their
weak convergence includes cap atoms. The established all-policy weak-value
comparison and duration-coefficient Lipschitz estimate give the joint limit;
no convergence or availability of a limiting policy is inferred from it.
-/

open MeasureTheory Set Filter
open scoped NNReal Topology Classical
namespace ProphetSecretary.Limiting.FiniteIntensityHybridInstance
open ProphetSecretary.Probability
variable {n : ℕ}

lemma capAt_individual_weak (B : FiniteIntensityHybridInstance n)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hKs : ∀ m, 0<Ks m) (hK : 0<K)
    (hLimit : Tendsto Ks atTop (𝓝 K)) (i : Fin n) :
    Tendsto (fun m => (B.capAt (Ks m) (hKs m)).individuals.marginalProbabilityLaw i) atTop
      (𝓝 ((B.capAt K hK).individuals.marginalProbabilityLaw i)) := by
  have h := probabilityMeasure_cap_tendsto (B.individuals.marginalProbabilityLaw i) (NNReal.tendsto_coe.2 hLimit)
  convert h using 1
  · funext m
    apply Subtype.ext
    rfl
  · congr 1

lemma capAt_intensity_weak (B : FiniteIntensityHybridInstance n)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hKs : ∀ m, 0<Ks m) (hK : 0<K)
    (hLimit : Tendsto Ks atTop (𝓝 K)) :
    Tendsto (fun m => (B.capAt (Ks m) (hKs m)).intensity) atTop (𝓝 (B.capAt K hK).intensity) :=
  finiteMeasure_cap_tendsto B.intensity (NNReal.tendsto_coe.2 hLimit)

lemma capAt_value_tendsto (B : FiniteIntensityHybridInstance n)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hKs : ∀ m, 0<Ks m) (hK : 0<K)
    (hLimit : Tendsto Ks atTop (𝓝 K)) {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    Tendsto (fun m => (B.capAt (Ks m) (hKs m)).optimalScalarValue w c) atTop
      (𝓝 ((B.capAt K hK).optimalScalarValue w c)) :=
  optimalScalarValue_tendsto_of_weak (fun m => B.capAt (Ks m) (hKs m)) (B.capAt K hK)
    B.cap (fun _ => le_rfl) le_rfl (fun _ => rfl)
    (B.capAt_individual_weak hKs hK hLimit) (B.capAt_intensity_weak hKs hK hLimit) hw hc

lemma capAt_value_tendsto_moving_duration (B : FiniteIntensityHybridInstance n)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hKs : ∀ m, 0<Ks m) (hK : 0<K)
    (hLimit : Tendsto Ks atTop (𝓝 K)) {cs : ℕ → ℝ} {c w : ℝ}
    (hcs : ∀ m, 0≤cs m) (hw : 0≤w) (hcLimit : Tendsto cs atTop (𝓝 c)) :
    Tendsto (fun m => (B.capAt (Ks m) (hKs m)).optimalScalarValue w (cs m)) atTop
      (𝓝 ((B.capAt K hK).optimalScalarValue w c)) := by
  have hWeak := optimalScalarValue_uniform_weak (fun m => B.capAt (Ks m) (hKs m)) (B.capAt K hK)
    B.cap ⟨w,hw⟩ (fun _ => le_rfl) le_rfl (fun _ => rfl)
    (B.capAt_individual_weak hKs hK hLimit) (B.capAt_intensity_weak hKs hK hLimit)
  have hDiff : Tendsto (fun m => (B.capAt (Ks m) (hKs m)).optimalScalarValue w (cs m)-
      (B.capAt K hK).optimalScalarValue w (cs m)) atTop (𝓝 (0:ℝ)) := by
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [hWeak ε hε] with m hm
    simpa only [Real.dist_eq,sub_zero] using hm w (cs m) hw le_rfl (hcs m)
  have hAbs : Tendsto (fun m => |cs m-c|) atTop (𝓝 (0:ℝ)) := by
    simpa only [sub_self,abs_zero] using (hcLimit.sub_const c).abs
  have hFixed : Tendsto (fun m => (B.capAt K hK).optimalScalarValue w (cs m)) atTop
      (𝓝 ((B.capAt K hK).optimalScalarValue w c)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hAbs
    intro m
    simpa only [Real.norm_eq_abs] using (B.capAt K hK).optimalScalarValue_duration_abs_sub_le w (cs m) c
  simpa only [sub_add_cancel,zero_add] using hDiff.add hFixed

end ProphetSecretary.Limiting.FiniteIntensityHybridInstance
