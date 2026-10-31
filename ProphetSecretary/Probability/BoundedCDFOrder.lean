import ProphetSecretary.Probability.BoundedCDFMean

/-!
# First-moment comparison from bounded distribution functions
-/
open MeasureTheory Set Filter
open scoped NNReal
namespace ProphetSecretary.Probability


lemma integrable_tail_on_bounded_interval {A : Type*} [MeasurableSpace A] (ρ : Measure A) [IsProbabilityMeasure ρ] (f : A → ℝ) (H : ℝ≥0) :
    IntegrableOn (fun t : ℝ => ρ.real {x | t < f x}) (Ioc (0 : ℝ) H) := by
  have hm : Antitone (fun t : ℝ => ρ.real {x | t < f x}) := fun _ _ hab => measureReal_mono (fun _ hx => hab.trans_lt hx)
  apply Integrable.of_bound hm.measurable.aestronglyMeasurable.restrict 1
  apply ae_of_all
  intro t
  rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
  exact measureReal_le_one

theorem integral_le_of_bounded_cdf_le {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    {X : Ω → ℝ} {Y : Ξ → ℝ} (hX : Measurable X) (hY : Measurable Y)
    (H : ℝ≥0) (hXR : ∀ᵐ x ∂μ, X x ∈ Icc (0 : ℝ) H) (hYR : ∀ᵐ y ∂ν, Y y ∈ Icc (0 : ℝ) H)
    (hCDF : ∀ t ∈ Ioc (0 : ℝ) H, μ.real {x | X x ≤ t} ≤ ν.real {y | Y y ≤ t}) :
    (∫ y, Y y ∂ν) ≤ ∫ x, X x ∂μ := by
  rw [integral_eq_bounded_strict_layercake ν hY H hYR,integral_eq_bounded_strict_layercake μ hX H hXR]
  apply integral_mono_ae (integrable_tail_on_bounded_interval ν Y H) (integrable_tail_on_bounded_interval μ X H)
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with t ht
  rw [probReal_gt_eq_one_sub_le ν hY,probReal_gt_eq_one_sub_le μ hX]
  exact sub_le_sub_left (hCDF t ht) 1

end ProphetSecretary.Probability
