import ProphetSecretary.Probability.CenteredValueScore
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.MeasureTheory.Measure.SubFinite

/-!
# First moments of weakly convergent bounded finite intensities

Clipping is a bounded continuous test equal to the mark on the common support.
This statement applies to finite measures without normalizing their masses.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Limiting

open ProphetSecretary.Probability

theorem finiteIntensity_firstMoment_tendsto {Γ : Type*} {l : Filter Γ}
    (μs : Γ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hsCap : ∀ m, ∀ᵐ x ∂(μs m : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hCap : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hWeak : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun m => ∫ x, x ∂(μs m : Measure ℝ)) l (𝓝 (∫ x, x ∂(μ : Measure ℝ))) := by
  have he (ν : FiniteMeasure ℝ) (hc : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) H) :
      (∫ x, boundedOfferValue H x ∂(ν : Measure ℝ)) = ∫ x, x ∂(ν : Measure ℝ) := by
    apply integral_congr_ae
    filter_upwards [hc] with x hx
    exact boundedOfferValue_eq H hx
  have h := FiniteMeasure.tendsto_iff_forall_integral_tendsto.mp hWeak (boundedOfferValue H)
  have hs : (fun m => ∫ x, boundedOfferValue H x ∂(μs m : Measure ℝ)) =
      (fun m => ∫ x, x ∂(μs m : Measure ℝ)) := funext (fun m => he (μs m) (hsCap m))
  rw [hs,he μ hCap] at h
  exact h

lemma finiteIntensity_integrable_mark (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hCap : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H) :
    Integrable (fun x : ℝ => x) (μ : Measure ℝ) := by
  apply Integrable.of_bound measurable_id.aestronglyMeasurable H
  filter_upwards [hCap] with x hx
  change ‖x‖ ≤ H
  rw [Real.norm_eq_abs,abs_of_nonneg hx.1]
  exact hx.2

lemma finiteIntensity_difference_firstMoment (μ ν : FiniteMeasure ℝ) (H : ℝ≥0)
    (hν : ∀ᵐ x ∂(ν : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hOrder : (μ : Measure ℝ) ≤ (ν : Measure ℝ)) :
    (∫ x, x ∂((ν : Measure ℝ)-(μ : Measure ℝ))) =
      (∫ x, x ∂(ν : Measure ℝ))-(∫ x, x ∂(μ : Measure ℝ)) := by
  have hI := finiteIntensity_integrable_mark ν H hν
  have hμI := hI.mono_measure hOrder
  have hδI := hI.mono_measure (Measure.sub_le : (ν : Measure ℝ)-(μ : Measure ℝ) ≤ (ν : Measure ℝ))
  have he := integral_add_measure hδI hμI
  rw [Measure.sub_add_cancel_of_le hOrder] at he
  linarith only [he]

theorem finiteIntensity_difference_firstMoment_tendsto {Γ : Type*} {l : Filter Γ}
    (μs : Γ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hsCap : ∀ m, ∀ᵐ x ∂(μs m : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hCap : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hOrder : ∀ m, (μ : Measure ℝ) ≤ (μs m : Measure ℝ))
    (hWeak : Tendsto μs l (𝓝 μ)) :
    Tendsto (fun m => ∫ x, x ∂((μs m : Measure ℝ)-(μ : Measure ℝ))) l (𝓝 (0 : ℝ)) := by
  have h := (finiteIntensity_firstMoment_tendsto μs μ H hsCap hCap hWeak).sub_const
    (∫ x, x ∂(μ : Measure ℝ))
  simp only [sub_self] at h
  have he : (fun m => ∫ x, x ∂((μs m : Measure ℝ)-(μ : Measure ℝ))) =
      (fun m => (∫ x, x ∂(μs m : Measure ℝ))-(∫ x, x ∂(μ : Measure ℝ))) :=
    funext (fun m => finiteIntensity_difference_firstMoment μ (μs m) H (hsCap m) (hOrder m))
  rwa [he]

end ProphetSecretary.Limiting
