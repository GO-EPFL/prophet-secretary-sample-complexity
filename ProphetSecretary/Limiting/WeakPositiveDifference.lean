import ProphetSecretary.Limiting.WeakMeasureOrder
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Weak limits of positive differences of finite measures

The order hypotheses are explicit positivity conditions for the actual
measure subtraction. Bounded continuous tests turn the exact positive-sum
identity into a difference of converging integrals.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology
namespace ProphetSecretary.Limiting

noncomputable def positiveFiniteDifference (ν μ : FiniteMeasure ℝ) : FiniteMeasure ℝ :=
  ⟨(ν : Measure ℝ)-(μ : Measure ℝ),isFiniteMeasure_of_le (ν : Measure ℝ) Measure.sub_le⟩

lemma positiveFiniteDifference_add (ν μ : FiniteMeasure ℝ) (hOrder : (μ : Measure ℝ)≤(ν : Measure ℝ)) :
    positiveFiniteDifference ν μ+μ=ν := by
  apply FiniteMeasure.toMeasure_injective
  rw [FiniteMeasure.toMeasure_add]
  exact Measure.sub_add_cancel_of_le hOrder

lemma integral_positiveFiniteDifference (ν μ : FiniteMeasure ℝ) (hOrder : (μ : Measure ℝ)≤(ν : Measure ℝ))
    (f : ℝ →ᵇ ℝ) :
    (∫ x, f x ∂(positiveFiniteDifference ν μ : Measure ℝ))=
      (∫ x, f x ∂(ν : Measure ℝ))-(∫ x, f x ∂(μ : Measure ℝ)) := by
  have h := integral_add_measure (f.integrable (positiveFiniteDifference ν μ : Measure ℝ)) (f.integrable (μ : Measure ℝ))
  change (∫ x, f x ∂((positiveFiniteDifference ν μ+μ : FiniteMeasure ℝ) : Measure ℝ))=_ at h
  rw [positiveFiniteDifference_add ν μ hOrder] at h
  linarith only [h]

theorem positiveFiniteDifference_tendsto {Γ : Type*} {l : Filter Γ}
    {νs μs : Γ → FiniteMeasure ℝ} {ν μ : FiniteMeasure ℝ}
    (hOrders : ∀ m, (μs m : Measure ℝ)≤(νs m : Measure ℝ))
    (hOrder : (μ : Measure ℝ)≤(ν : Measure ℝ))
    (hν : Tendsto νs l (𝓝 ν)) (hμ : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun m => positiveFiniteDifference (νs m) (μs m)) l (𝓝 (positiveFiniteDifference ν μ)) := by
  apply FiniteMeasure.tendsto_of_forall_integral_tendsto
  intro f
  have h := (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hν f).sub
    (FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hμ f)
  simp_rw [integral_positiveFiniteDifference _ _ (hOrders _),integral_positiveFiniteDifference _ _ hOrder]
  exact h

end ProphetSecretary.Limiting
