import ProphetSecretary.Limiting.Compensator

/-!
# Duration indicator in the constructed Palm identity

For an analytical measurable duration functional, the independent test point
integrates to band intensity times expected duration. Actual stopping-policy
applications separately prove that its deleted-execution count equals reached points.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting

variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def durationKernel (τ : World Seed → ℝ) (B : Set ℝ) (q : Point × World Seed) : ℝ≥0∞ :=
  if q.1.2 ∈ B ∧ q.1.1 ≤ τ q.2 then 1 else 0

lemma measurable_durationKernel (τ : World Seed → ℝ) (hτ : Measurable τ)
    {B : Set ℝ} (hB : MeasurableSet B) : Measurable (durationKernel τ B) := by
  have hband : MeasurableSet {q : Point × World Seed | q.1.2 ∈ B} :=
    hB.preimage (measurable_snd.comp measurable_fst)
  exact Measurable.ite (hband.inter (measurableSet_le (measurable_fst.comp measurable_fst)
    (hτ.comp measurable_snd))) measurable_const measurable_const

lemma lintegral_durationKernel (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (τ : World Seed → ℝ) (hτ : Measurable τ)
    (hunit : ∀ᵐ v ∂worldLaw μ ν, τ v ∈ Icc (0 : ℝ) 1)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫⁻ q, durationKernel τ B q ∂(intensity μ).prod (worldLaw μ ν)) =
      (μ : Measure ℝ) B * ENNReal.ofReal (∫ v, τ v ∂worldLaw μ ν) := by
  have hτi : Integrable τ (worldLaw μ ν) := by
    apply Integrable.of_bound hτ.aestronglyMeasurable 1
    filter_upwards [hunit] with v hv
    simpa only [Real.norm_eq_abs, abs_of_nonneg hv.1] using hv.2
  have hinner : ∀ᵐ v ∂worldLaw μ ν,
      (∫⁻ p, durationKernel τ B (p, v) ∂intensity μ) = ENNReal.ofReal (τ v) * (μ : Measure ℝ) B := by
    filter_upwards [hunit] with v hv
    have he : (fun p : Point => durationKernel τ B (p, v)) = (Iic (τ v) ×ˢ B).indicator 1 := by
      funext p
      simp [durationKernel, Set.indicator_apply, and_comm]
    rw [he, lintegral_indicator_one (measurableSet_Iic.prod hB), intensity, Measure.prod_prod, uniformClock_Iic hv]
  have hof := ofReal_integral_eq_lintegral_ofReal hτi (hunit.mono (fun _ h => h.1))
  calc
    _ = ∫⁻ v, ∫⁻ p, durationKernel τ B (p, v) ∂intensity μ ∂worldLaw μ ν :=
      lintegral_prod_symm _ (measurable_durationKernel τ hτ hB).aemeasurable
    _ = ∫⁻ v, ENNReal.ofReal (τ v) * (μ : Measure ℝ) B ∂worldLaw μ ν := lintegral_congr_ae hinner
    _ = (∫⁻ v, ENNReal.ofReal (τ v) ∂worldLaw μ ν) * (μ : Measure ℝ) B :=
      lintegral_mul_const _ hτ.ennreal_ofReal
    _ = _ := by rw [← hof]; exact mul_comm _ _

lemma mecke_durationKernel (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (τ : World Seed → ℝ) (hτ : Measurable τ)
    (hunit : ∀ᵐ v ∂worldLaw μ ν, τ v ∈ Icc (0 : ℝ) 1)
    {B : Set ℝ} (hB : MeasurableSet B) :
    (∫⁻ v, meckeSum (durationKernel τ B) v ∂worldLaw μ ν) =
      (μ : Measure ℝ) B * ENNReal.ofReal (∫ v, τ v ∂worldLaw μ ν) :=
  (mecke μ ν _ (measurable_durationKernel τ hτ hB)).trans (lintegral_durationKernel μ ν τ hτ hunit hB)

end ProphetSecretary.Limiting
