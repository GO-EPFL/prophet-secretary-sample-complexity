import ProphetSecretary.Reach.ReachIntegralBounds
import Mathlib.Probability.Independence.Basic

open MeasureTheory Set ProbabilityTheory

namespace ProphetSecretary.Reach

/-- Independence factors the joint law of a pending duration and the candidate's
uniform clock. This is an analytic change of variables, to be applied after
constructing the pending execution. -/
theorem integral_independent_uniform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {σ U : Ω → ℝ}
    (hσ : Measurable σ) (hU : Measurable U)
    (hLaw : μ.map U = volume.restrict (Icc (0 : ℝ) 1))
    (hind : IndepFun σ U μ) {f : ℝ × ℝ → ℝ} (hf : Measurable f)
    (hInt : Integrable f ((μ.map σ).prod (volume.restrict (Icc (0 : ℝ) 1)))) :
    (∫ ω, f (σ ω, U ω) ∂μ) =
      ∫ s, (∫ t in Icc (0 : ℝ) 1, f (s, t)) ∂μ.map σ := by
  haveI : IsProbabilityMeasure (μ.map σ) := Measure.isProbabilityMeasure_map hσ.aemeasurable
  have hjoint : μ.map (fun ω ↦ (σ ω, U ω)) =
      (μ.map σ).prod (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [hind.map_prod_eq_prod_map_map hσ.aemeasurable hU.aemeasurable, hLaw]
  calc
    _ = ∫ z, f z ∂μ.map (fun ω ↦ (σ ω, U ω)) :=
      (integral_map (hσ.prodMk hU).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(μ.map σ).prod (volume.restrict (Icc (0 : ℝ) 1)) := by rw [hjoint]
    _ = _ := integral_prod _ hInt

/-- The reach probability is the expected pending duration whenever the
candidate clock is uniform and independent of that duration. -/
theorem reach_probability_eq_mean_pending {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {σ U : Ω → ℝ}
    (hσ : Measurable σ) (hU : Measurable U)
    (hLaw : μ.map U = volume.restrict (Icc (0 : ℝ) 1))
    (hind : IndepFun σ U μ)
    (hσ01 : ∀ᵐ ω ∂μ, σ ω ∈ Icc (0 : ℝ) 1) :
    μ.real {ω | U ω ≤ σ ω} = ∫ ω, σ ω ∂μ := by
  classical
  haveI : IsProbabilityMeasure (μ.map σ) := Measure.isProbabilityMeasure_map hσ.aemeasurable
  have hsMap : ∀ᵐ s ∂μ.map σ, s ∈ Icc (0 : ℝ) 1 :=
    (ae_map_iff hσ.aemeasurable measurableSet_Icc).mpr hσ01
  let f : ℝ × ℝ → ℝ := fun z ↦ if z.2 ≤ z.1 then 1 else 0
  have hf : Measurable f :=
    Measurable.ite (measurableSet_le measurable_snd measurable_fst) measurable_const measurable_const
  have hInt : Integrable f ((μ.map σ).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    apply (integrable_const (1 : ℝ)).mono' hf.aestronglyMeasurable
    filter_upwards [] with z
    dsimp [f]
    split_ifs <;> norm_num
  have hchange := integral_independent_uniform μ hσ hU hLaw hind hf hInt
  have hinner : (∫ s, (∫ t in Icc (0 : ℝ) 1, f (s, t)) ∂μ.map σ) =
      ∫ s, s ∂μ.map σ := by
    apply integral_congr_ae
    filter_upwards [hsMap] with s hs
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact integral_reach_clock hs.1 hs.2
  rw [hinner, integral_map (f := fun s : ℝ ↦ s) hσ.aemeasurable measurable_id.aestronglyMeasurable] at hchange
  have hevent : MeasurableSet {ω | U ω ≤ σ ω} := measurableSet_le hU hσ
  have hindicator : (∫ ω, f (σ ω, U ω) ∂μ) = μ.real {ω | U ω ≤ σ ω} := by
    simpa only [f, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
      (integral_indicator_one (μ := μ) hevent)
  exact hindicator.symm.trans hchange

/-- Bounded measurable real random variables on a probability space are
integrable; the bounds are only required almost surely. -/
theorem integrable_of_ae_unit {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {f : Ω → ℝ}
    (hf : AEStronglyMeasurable f μ) (hb : ∀ᵐ ω ∂μ, f ω ∈ Icc (0 : ℝ) 1) :
    Integrable f μ := by
  apply (integrable_const (1 : ℝ)).mono' hf
  filter_upwards [hb] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2

/-- Exact expected duration until the earlier of an independent uniform
candidate clock and an almost surely unit-bounded pending duration. -/
theorem mean_min_independent_uniform {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {σ U : Ω → ℝ}
    (hσ : Measurable σ) (hU : Measurable U)
    (hLaw : μ.map U = volume.restrict (Icc (0 : ℝ) 1))
    (hind : IndepFun σ U μ)
    (hσ01 : ∀ᵐ ω ∂μ, σ ω ∈ Icc (0 : ℝ) 1) :
    (∫ ω, min (U ω) (σ ω) ∂μ) = ∫ ω, (σ ω - σ ω ^ 2 / 2) ∂μ := by
  haveI : IsProbabilityMeasure (μ.map σ) := Measure.isProbabilityMeasure_map hσ.aemeasurable
  have hU01 : ∀ᵐ ω ∂μ, U ω ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hU.aemeasurable measurableSet_Icc).mp
    rw [hLaw]
    exact ae_restrict_mem measurableSet_Icc
  have hmin01 : ∀ᵐ ω ∂μ, min (U ω) (σ ω) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hU01, hσ01] with ω hu hs
    exact ⟨le_min hu.1 hs.1, (min_le_left _ _).trans hu.2⟩
  have hminInt := integrable_of_ae_unit μ (hU.min hσ).aestronglyMeasurable hmin01
  let f : ℝ × ℝ → ℝ := fun z ↦ min z.2 z.1
  have hf : Measurable f := (continuous_snd.min continuous_fst).measurable
  have hjoint : μ.map (fun ω ↦ (σ ω, U ω)) =
      (μ.map σ).prod (volume.restrict (Icc (0 : ℝ) 1)) := by
    rw [hind.map_prod_eq_prod_map_map hσ.aemeasurable hU.aemeasurable, hLaw]
  have hInt : Integrable f ((μ.map σ).prod (volume.restrict (Icc (0 : ℝ) 1))) := by
    rw [← hjoint]
    exact (integrable_map_measure hf.aestronglyMeasurable (hσ.prodMk hU).aemeasurable).mpr hminInt
  have hchange := integral_independent_uniform μ hσ hU hLaw hind hf hInt
  have hsMap : ∀ᵐ s ∂μ.map σ, s ∈ Icc (0 : ℝ) 1 :=
    (ae_map_iff hσ.aemeasurable measurableSet_Icc).mpr hσ01
  have hinner : (∫ s, (∫ t in Icc (0 : ℝ) 1, f (s, t)) ∂μ.map σ) =
      ∫ s, (s - s ^ 2 / 2) ∂μ.map σ := by
    apply integral_congr_ae
    filter_upwards [hsMap] with s hs
    rw [integral_Icc_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (zero_le_one : (0 : ℝ) ≤ 1)]
    exact integral_min_clock hs.1 hs.2
  rw [hinner, integral_map (f := fun s : ℝ ↦ s - s ^ 2 / 2) hσ.aemeasurable
    (continuous_id.sub ((continuous_id.pow 2).div_const 2)).measurable.aestronglyMeasurable] at hchange
  exact hchange

/-- The universal reach--duration estimate once the pending execution has
been constructed. All bounds and the pathwise comparison may hold almost surely. -/
theorem mean_pending_le_twice_duration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {σ U τ : Ω → ℝ}
    (hσ : Measurable σ) (hU : Measurable U) (hτ : AEStronglyMeasurable τ μ)
    (hLaw : μ.map U = volume.restrict (Icc (0 : ℝ) 1))
    (hind : IndepFun σ U μ)
    (hσ01 : ∀ᵐ ω ∂μ, σ ω ∈ Icc (0 : ℝ) 1)
    (hτ01 : ∀ᵐ ω ∂μ, τ ω ∈ Icc (0 : ℝ) 1)
    (hmin : ∀ᵐ ω ∂μ, min (U ω) (σ ω) ≤ τ ω) :
    (∫ ω, σ ω ∂μ) ≤ 2 * ∫ ω, τ ω ∂μ := by
  have hσInt := integrable_of_ae_unit μ hσ.aestronglyMeasurable hσ01
  have hτInt := integrable_of_ae_unit μ hτ hτ01
  have hU01 : ∀ᵐ ω ∂μ, U ω ∈ Icc (0 : ℝ) 1 := by
    apply (ae_map_iff hU.aemeasurable measurableSet_Icc).mp
    rw [hLaw]
    exact ae_restrict_mem measurableSet_Icc
  have hmin01 : ∀ᵐ ω ∂μ, min (U ω) (σ ω) ∈ Icc (0 : ℝ) 1 := by
    filter_upwards [hU01, hσ01] with ω hu hs
    exact ⟨le_min hu.1 hs.1, (min_le_left _ _).trans hu.2⟩
  have hminInt := integrable_of_ae_unit μ (hU.min hσ).aestronglyMeasurable hmin01
  have hσ2Int : Integrable (fun ω ↦ σ ω ^ 2) μ := by
    apply integrable_of_ae_unit μ (hσ.aestronglyMeasurable.pow 2)
    filter_upwards [hσ01] with ω hs
    refine ⟨sq_nonneg _, ?_⟩
    change σ ω ^ 2 ≤ 1
    nlinarith [hs.1, hs.2]
  have hbound : (∫ ω, σ ω ∂μ) / 2 ≤ ∫ ω, min (U ω) (σ ω) ∂μ := by
    rw [mean_min_independent_uniform μ hσ hU hLaw hind hσ01]
    have h := integral_mono_ae (hσInt.div_const 2) (hσInt.sub (hσ2Int.div_const 2)) ?_
    · simpa only [integral_div, Pi.sub_apply] using h
    · filter_upwards [hσ01] with ω hs
      change σ ω / 2 ≤ σ ω - σ ω ^ 2 / 2
      nlinarith [mul_nonneg hs.1 (sub_nonneg.mpr hs.2)]
  have hcomp := integral_mono_ae hminInt hτInt hmin
  linarith

/-- The probability formulation of the universal reach--duration comparison.
Policy-specific work must construct `σ` and establish its independence. -/
theorem reach_probability_le_twice_duration {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {σ U τ : Ω → ℝ}
    (hσ : Measurable σ) (hU : Measurable U) (hτ : AEStronglyMeasurable τ μ)
    (hLaw : μ.map U = volume.restrict (Icc (0 : ℝ) 1))
    (hind : IndepFun σ U μ)
    (hσ01 : ∀ᵐ ω ∂μ, σ ω ∈ Icc (0 : ℝ) 1)
    (hτ01 : ∀ᵐ ω ∂μ, τ ω ∈ Icc (0 : ℝ) 1)
    (hmin : ∀ᵐ ω ∂μ, min (U ω) (σ ω) ≤ τ ω) :
    μ.real {ω | U ω ≤ σ ω} ≤ 2 * ∫ ω, τ ω ∂μ := by
  rw [reach_probability_eq_mean_pending μ hσ hU hLaw hind hσ01]
  exact mean_pending_le_twice_duration μ hσ hU hτ hLaw hind hσ01 hτ01 hmin

end ProphetSecretary.Reach
