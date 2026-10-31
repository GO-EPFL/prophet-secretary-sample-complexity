import ProphetSecretary.Probability.WeakStopLoss

/-!
# Moving excess thresholds under weak finite-measure convergence

The clipped excess kernel is bounded continuous in the offer and 1-Lipschitz
in its threshold. Weak convergence also controls total mass, so moving the
threshold costs a vanishing mass-times-displacement error. Atoms at the limiting
threshold are permitted because the excess kernel is continuous there.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal
namespace ProphetSecretary.Probability

noncomputable def finiteClippedStopLoss (μ : FiniteMeasure ℝ) (H : ℝ≥0) (q : ℝ) : ℝ :=
  ∫ x, boundedStopLossTest H q x ∂(μ : Measure ℝ)

lemma finiteClippedStopLoss_lipschitz_threshold (μ : FiniteMeasure ℝ) (H : ℝ≥0) (q r : ℝ) :
    |finiteClippedStopLoss μ H q-finiteClippedStopLoss μ H r|≤(μ : Measure ℝ).real univ*|q-r| := by
  unfold finiteClippedStopLoss
  rw [←integral_sub ((boundedStopLossTest H q).integrable _) ((boundedStopLossTest H r).integrable _)]
  have h := norm_integral_le_of_norm_le_const (μ:=(μ : Measure ℝ))
    (f:=fun x => boundedStopLossTest H q x-boundedStopLossTest H r x)
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using boundedStopLossTest_lipschitz_threshold H x q r)
  rw [mul_comm] at h
  simpa only [Real.norm_eq_abs] using h

lemma finiteClippedStopLoss_tendsto_moving {ι : Type*} {l : Filter ι}
    {μs : ι → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} (hμ : Tendsto μs l (𝓝 μ))
    (H : ℝ≥0) {qs : ι → ℝ} {q : ℝ} (hq : Tendsto qs l (𝓝 q)) :
    Tendsto (fun m => finiteClippedStopLoss (μs m) H (qs m)) l (𝓝 (finiteClippedStopLoss μ H q)) := by
  have hFixed : Tendsto (fun m => finiteClippedStopLoss (μs m) H q) l (𝓝 (finiteClippedStopLoss μ H q)) :=
    FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (boundedStopLossTest H q)
  have hMass : Tendsto (fun m => (μs m : Measure ℝ).real univ) l (𝓝 ((μ : Measure ℝ).real univ)) := by
    have h := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ (BoundedContinuousFunction.const ℝ (1:ℝ))
    simpa only [BoundedContinuousFunction.const_apply,integral_const,smul_eq_mul,mul_one] using h
  have hBound : Tendsto (fun m => (μs m : Measure ℝ).real univ*|qs m-q|) l (𝓝 (0:ℝ)) := by
    simpa only [sub_self,abs_zero,mul_zero] using hMass.mul (hq.sub_const q).abs
  have hAbs : Tendsto (fun m => |finiteClippedStopLoss (μs m) H (qs m)-finiteClippedStopLoss (μs m) H q|) l (𝓝 (0:ℝ)) :=
    squeeze_zero (fun _ => abs_nonneg _) (fun m => finiteClippedStopLoss_lipschitz_threshold (μs m) H (qs m) q) hBound
  have hDiff : Tendsto (fun m => finiteClippedStopLoss (μs m) H (qs m)-finiteClippedStopLoss (μs m) H q) l (𝓝 (0:ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    simpa only [sub_zero,Real.norm_eq_abs] using hAbs
  simpa only [sub_add_cancel,zero_add] using hDiff.add hFixed

lemma finiteIntensity_stopLoss_tendsto_moving {ι : Type*} {l : Filter ι}
    {μs : ι → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} (hμ : Tendsto μs l (𝓝 μ))
    (H : ℝ≥0) (hsCap : ∀ m, ∀ᵐ x ∂(μs m : Measure ℝ), x∈Icc (0:ℝ) H)
    (hCap : ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0:ℝ) H)
    {qs : ι → ℝ} {q : ℝ} (hq : Tendsto qs l (𝓝 q)) :
    Tendsto (fun m => Model.stopLoss (μs m : Measure ℝ) (qs m)) l (𝓝 (Model.stopLoss (μ : Measure ℝ) q)) := by
  have hEq (ν : FiniteMeasure ℝ) (hν : ∀ᵐ x ∂(ν : Measure ℝ), x∈Icc (0:ℝ) H) (c : ℝ) :
      finiteClippedStopLoss ν H c=Model.stopLoss (ν : Measure ℝ) c := by
    apply integral_congr_ae
    filter_upwards [hν] with x hx
    change max 0 (boundedOfferValue H x-c)=max 0 (x-c)
    rw [boundedOfferValue_eq H hx]
  have h := finiteClippedStopLoss_tendsto_moving hμ H hq
  have hFun : (fun m => finiteClippedStopLoss (μs m) H (qs m))=(fun m => Model.stopLoss (μs m : Measure ℝ) (qs m)) :=
    funext fun m => hEq (μs m) (hsCap m) (qs m)
  rwa [hFun,hEq μ hCap q] at h

end ProphetSecretary.Probability
