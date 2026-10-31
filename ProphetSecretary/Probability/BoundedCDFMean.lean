import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Bounded first moments from almost-everywhere distribution-function convergence

The probability spaces may vary with the index. The common bounded support
reduces layer cake to one finite time interval, where dominated convergence
applies to the actual tail probabilities. No coupling or policy convergence
is asserted by this first-moment statement.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal
namespace ProphetSecretary.Probability

lemma probReal_gt_eq_one_sub_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {X : Ω → ℝ} (hX : Measurable X) (t : ℝ) :
    μ.real {x | t < X x} = 1-μ.real {x | X x ≤ t} := by
  have he : {x | t < X x} = ({x | X x ≤ t} : Set Ω)ᶜ := by ext x; simp
  rw [he,probReal_compl_eq_one_sub (measurableSet_le hX measurable_const)]

lemma integral_eq_bounded_strict_layercake {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {X : Ω → ℝ} (hX : Measurable X) (H : ℝ≥0)
    (hRange : ∀ᵐ x ∂μ, X x ∈ Icc (0 : ℝ) H) :
    (∫ x, X x ∂μ) = ∫ t in Ioc (0 : ℝ) H, μ.real {x | t < X x} := by
  have hI : Integrable X μ := by
    apply Integrable.of_bound hX.aestronglyMeasurable H
    exact hRange.mono fun x hx => by simpa only [Real.norm_eq_abs,abs_of_nonneg hx.1] using hx.2
  rw [hI.integral_eq_integral_meas_lt (hRange.mono fun _ h => h.1)]
  have hzero (t : ℝ) (ht : (H : ℝ) < t) : μ.real {x | t < X x} = 0 := by
    apply (measureReal_eq_zero_iff (measure_ne_top _ _)).mpr
    apply measure_eq_zero_iff_ae_notMem.mpr
    exact hRange.mono fun _ hx => not_lt_of_ge (hx.2.trans ht.le)
  have heq : (fun t : ℝ => μ.real {x | t < X x}) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      (Ioc (0 : ℝ) H).indicator (fun t => μ.real {x | t < X x}) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht0
    by_cases htH : t ≤ (H : ℝ)
    · rw [Set.indicator_of_mem (show t ∈ Ioc (0 : ℝ) H from ⟨ht0,htH⟩)]
    · rw [Set.indicator_of_notMem (show t ∉ Ioc (0 : ℝ) H from fun h => htH h.2),hzero t (not_le.mp htH)]
  calc
    _ = ∫ t in Ioi (0 : ℝ), (Ioc (0 : ℝ) H).indicator (fun t => μ.real {x | t < X x}) t := integral_congr_ae heq
    _ = ∫ t in Ioc (0 : ℝ) H, μ.real {x | t < X x} := by
      rw [integral_indicator measurableSet_Ioc,Measure.restrict_restrict measurableSet_Ioc,
        inter_eq_left.mpr Ioc_subset_Ioi_self]

/-- Bounded benchmark expectations converge from the actual CDFs even when
finite-instance dimensions and probability spaces vary with the sequence. -/
theorem tendsto_integrals_of_bounded_cdf {Γ : Type*} {l : Filter Γ} [l.IsCountablyGenerated]
    {Ω : Γ → Type*} [∀ m, MeasurableSpace (Ω m)] (μ : ∀ m, Measure (Ω m)) [∀ m, IsProbabilityMeasure (μ m)]
    {Ξ : Type*} [MeasurableSpace Ξ] (ν : Measure Ξ) [IsProbabilityMeasure ν]
    (X : ∀ m, Ω m → ℝ) (Y : Ξ → ℝ) (hX : ∀ m, Measurable (X m)) (hY : Measurable Y)
    (H : ℝ≥0) (hXR : ∀ m, ∀ᵐ x ∂μ m, X m x ∈ Icc (0 : ℝ) H)
    (hYR : ∀ᵐ y ∂ν, Y y ∈ Icc (0 : ℝ) H)
    (hCDF : ∀ᵐ t ∂volume.restrict (Ioc (0 : ℝ) H),
      Tendsto (fun m => (μ m).real {x | X m x ≤ t}) l (𝓝 (ν.real {y | Y y ≤ t}))) :
    Tendsto (fun m => ∫ x, X m x ∂μ m) l (𝓝 (∫ y, Y y ∂ν)) := by
  let T := volume.restrict (Ioc (0 : ℝ) H)
  let F : Γ → ℝ → ℝ := fun m t => (μ m).real {x | t < X m x}
  let G : ℝ → ℝ := fun t => ν.real {y | t < Y y}
  have hFm (m : Γ) : Antitone (F m) := fun a b hab => measureReal_mono (fun x hx => hab.trans_lt hx)
  have hMeas : ∀ᶠ m in l, AEStronglyMeasurable (F m) T :=
    Eventually.of_forall fun m => (hFm m).measurable.aestronglyMeasurable.restrict
  have hBound : ∀ᶠ m in l, ∀ᵐ t ∂T, ‖F m t‖ ≤ (1 : ℝ) :=
    Eventually.of_forall fun m => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs,abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hLim : ∀ᵐ t ∂T, Tendsto (fun m => F m t) l (𝓝 (G t)) := by
    filter_upwards [hCDF] with t ht
    simpa only [F,G,probReal_gt_eq_one_sub_le _ (hX _) t,probReal_gt_eq_one_sub_le ν hY t] using
      (tendsto_const_nhds.sub ht)
  have hDCT := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1 : ℝ)) hMeas hBound (integrable_const 1) hLim
  have hEq (m : Γ) : (∫ x, X m x ∂μ m) = ∫ t, F m t ∂T := integral_eq_bounded_strict_layercake (μ m) (hX m) H (hXR m)
  have hEqlim : (∫ y, Y y ∂ν) = ∫ t, G t ∂T := integral_eq_bounded_strict_layercake ν hY H hYR
  simpa only [← hEq,← hEqlim] using hDCT

end ProphetSecretary.Probability
