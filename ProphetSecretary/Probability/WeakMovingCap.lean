import ProphetSecretary.Probability.WeakFiniteStopLoss
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak continuity when a fixed finite law is capped at a moving height

A bounded continuous test stays bounded by its own uniform norm. Dominated
convergence therefore proves weak convergence of the capped laws, including
atoms exactly at the limiting cap.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology
namespace ProphetSecretary.Probability

lemma integral_moving_min_tendsto (μ : Measure ℝ) [IsFiniteMeasure μ] (f : ℝ →ᵇ ℝ)
    {qs : ℕ → ℝ} {q : ℝ} (hq : Tendsto qs atTop (𝓝 q)) :
    Tendsto (fun m => ∫ x, f (min x (qs m)) ∂μ) atTop (𝓝 (∫ x, f (min x q) ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ : ℝ => ‖f‖)
  · intro m
    exact (f.continuous.comp (continuous_id.min continuous_const)).measurable.aestronglyMeasurable
  · exact integrable_const _
  · intro m
    exact Eventually.of_forall fun x => f.norm_coe_le_norm _
  · exact Eventually.of_forall fun x => (f.continuous.tendsto (min x q)).comp (tendsto_const_nhds.min hq)

lemma finiteMeasure_cap_tendsto (μ : FiniteMeasure ℝ) {qs : ℕ → ℝ} {q : ℝ} (hq : Tendsto qs atTop (𝓝 q)) :
    Tendsto (fun m => μ.map (fun x => min x (qs m))) atTop (𝓝 (μ.map (fun x => min x q))) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have hEq (c : ℝ) : (∫ y, f y ∂(μ.map (fun x => min x c) : Measure ℝ))=
      ∫ x, f (min x c) ∂(μ : Measure ℝ) := by
    change (∫ y, f y ∂(μ : Measure ℝ).map (fun x => min x c))=_
    exact integral_map (measurable_id.min measurable_const).aemeasurable f.continuous.measurable.aestronglyMeasurable
  have hFun : (fun m => ∫ y, f y ∂(μ.map (fun x => min x (qs m)) : Measure ℝ))=
      (fun m => ∫ x, f (min x (qs m)) ∂(μ : Measure ℝ)) := funext fun m => hEq (qs m)
  rw [hFun,hEq q]
  exact integral_moving_min_tendsto (μ : Measure ℝ) f hq

lemma probabilityMeasure_cap_tendsto (μ : ProbabilityMeasure ℝ) {qs : ℕ → ℝ} {q : ℝ}
    (hq : Tendsto qs atTop (𝓝 q)) :
    Tendsto (fun m => μ.map (measurable_id.min (measurable_const : Measurable (fun _ : ℝ => qs m))).aemeasurable)
      atTop (𝓝 (μ.map (measurable_id.min (measurable_const : Measurable (fun _ : ℝ => q))).aemeasurable)) := by
  apply (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto).mpr
  intro f
  have hEq (c : ℝ) : (∫ y, f y ∂(μ.map (measurable_id.min (measurable_const : Measurable (fun _ : ℝ => c))).aemeasurable : Measure ℝ))=
      ∫ x, f (min x c) ∂(μ : Measure ℝ) := by
    change (∫ y, f y ∂(μ : Measure ℝ).map (fun x => min x c))=_
    exact integral_map (measurable_id.min measurable_const).aemeasurable f.continuous.measurable.aestronglyMeasurable
  have hFun : (fun m => ∫ y, f y ∂(μ.map (measurable_id.min (measurable_const : Measurable (fun _ : ℝ => qs m))).aemeasurable : Measure ℝ))=
      (fun m => ∫ x, f (min x (qs m)) ∂(μ : Measure ℝ)) := funext fun m => hEq (qs m)
  rw [hFun,hEq q]
  exact integral_moving_min_tendsto (μ : Measure ℝ) f hq

end ProphetSecretary.Probability
