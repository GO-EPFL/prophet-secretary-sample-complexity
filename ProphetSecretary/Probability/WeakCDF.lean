import ProphetSecretary.Probability.WeakFiniteAlmostContinuousIntegral
import Mathlib.MeasureTheory.Measure.Portmanteau

/-!
# Continuity-level probabilities for weak finite laws

The exceptional levels are actual atoms of the limiting finite measure and
form a countable, hence Lebesgue-null, set. Zero limiting mass is included.
-/
open MeasureTheory Set Filter
open scoped Topology
namespace ProphetSecretary.Probability

lemma atom_zero_volume_ae (μ : FiniteMeasure ℝ) : ∀ᵐ t ∂volume, (μ : Measure ℝ) {t} = 0 := by
  have hc : {t : ℝ | 0 < (μ : Measure ℝ) {t}}.Countable := by
    simpa only [id_eq,show ∀ t : ℝ, {x : ℝ | x = t} = {t} from fun _ => by ext; simp] using
      (Measure.countable_meas_level_set_pos (μ := (μ : Measure ℝ)) measurable_id)
  filter_upwards [hc.ae_notMem volume] with t ht
  exact le_antisymm (not_lt.mp ht) bot_le

lemma continuousAt_indicator_Ioi_one {t x : ℝ} (h : x ≠ t) :
    ContinuousAt ((Ioi t).indicator (fun _ : ℝ => (1 : ℝ))) x := by
  rcases lt_or_gt_of_ne h with hlt | hgt
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (0 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [eventually_lt_nhds hlt] with y hy
    exact indicator_of_notMem (show y ∉ Ioi t from not_lt.mpr hy.le) _
  · apply (continuousAt_const : ContinuousAt (fun _ : ℝ => (1 : ℝ)) x).congr_of_eventuallyEq
    filter_upwards [eventually_gt_nhds hgt] with y hy
    exact indicator_of_mem (show y ∈ Ioi t from hy) _

/-- A continuity tail level of the limiting measure gives convergence of its
actual real-valued upper-tail masses. -/
theorem finiteMeasure_real_Ioi_tendsto {Γ : Type*} {l : Filter Γ} [l.IsCountablyGenerated]
    {μs : Γ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ} (hweak : Tendsto μs l (𝓝 μ))
    {t : ℝ} (ht : (μ : Measure ℝ) {t} = 0) :
    Tendsto (fun m => (μs m : Measure ℝ).real (Ioi t)) l (𝓝 ((μ : Measure ℝ).real (Ioi t))) := by
  have hc : ∀ᵐ x ∂(μ : Measure ℝ), ContinuousAt ((Ioi t).indicator (fun _ : ℝ => (1 : ℝ))) x := by
    filter_upwards [measure_eq_zero_iff_ae_notMem.mp ht] with x hx
    exact continuousAt_indicator_Ioi_one (by simpa only [mem_singleton_iff] using hx)
  have hb : ∀ x : ℝ, |(Ioi t).indicator (fun _ : ℝ => (1 : ℝ)) x| ≤ (1 : ℝ) := by
    intro x
    by_cases hx : x ∈ Ioi t <;> simp [hx]
  have h := finite_integral_tendsto_of_weak_ae_continuous_bounded hweak
    (measurable_const.indicator measurableSet_Ioi) hb hc
  simpa only [← Pi.one_def,integral_indicator_one measurableSet_Ioi] using h

end ProphetSecretary.Probability
