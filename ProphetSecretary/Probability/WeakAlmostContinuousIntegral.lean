import ProphetSecretary.Probability.WeakLevelProbability
import ProphetSecretary.Probability.CenteredRangeScore
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Weak convergence of bounded almost continuous payoffs

The payoff need only be continuous almost everywhere for the limiting law.
The proof uses null level boundaries, the actual continuity-set theorem,
bounded layer-cake integration and dominated convergence. It does not assume
that value convergence alone establishes convergence of executed policies.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Probability

variable {Ω Γ : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω] [OpensMeasurableSpace Ω]

omit [TopologicalSpace Ω] [OpensMeasurableSpace Ω] in
/-- Exceptional payoff levels are countable and therefore null for Lebesgue
integration, even when the offer laws contain atoms. -/
lemma ae_null_payoff_level (μ : Measure Ω) [IsFiniteMeasure μ] {f : Ω → ℝ} (hf : Measurable f)
    (ν : Measure ℝ) [NullSingletonClass ν] : ∀ᵐ t ∂ν, μ {x | f x = t} = 0 := by
  have hs := Measure.countable_meas_level_set_pos (μ := μ) hf
  have hn := measure_eq_zero_iff_ae_notMem.mp (hs.measure_zero ν)
  filter_upwards [hn] with t ht
  exact le_antisymm (not_lt.mp ht) bot_le

/-- A bounded nonnegative payoff continuous at almost every limiting
configuration has convergent expectations under actual weakly convergent laws. -/
theorem integral_tendsto_of_weak_ae_continuous_range [HasOuterApproxClosed Ω]
    {l : Filter Γ} [l.IsCountablyGenerated] {μs : Γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hweak : Tendsto μs l (𝓝 μ)) {f : Ω → ℝ} (hf : Measurable f) {H : ℝ}
    (hbound : ∀ x, f x ∈ Icc (0 : ℝ) H)
    (hc : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt f x) :
    Tendsto (fun m => ∫ x, f x ∂(μs m : Measure Ω)) l (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  let ν := volume.restrict (Ioc (0 : ℝ) H)
  let F : ProbabilityMeasure Ω → ℝ → ℝ := fun P t => (P : Measure Ω).real {x | t ≤ f x}
  have heq (P : ProbabilityMeasure Ω) : (∫ x, f x ∂(P : Measure Ω)) = ∫ t, F P t ∂ν := by
    exact (integrable_of_range (P : Measure Ω) hf hbound).integral_eq_integral_Ioc_meas_le
      (Eventually.of_forall fun x => (hbound x).1) (Eventually.of_forall fun x => (hbound x).2)
  have hfm (P : ProbabilityMeasure Ω) : Antitone (F P) :=
    fun a b hab => measureReal_mono (fun x hx => hab.trans hx)
  have hF : ∀ᶠ m in l, AEStronglyMeasurable (F (μs m)) ν :=
    Eventually.of_forall fun m => (hfm (μs m)).measurable.aestronglyMeasurable.restrict
  have hFb : ∀ᶠ m in l, ∀ᵐ t ∂ν, ‖F (μs m) t‖ ≤ (1 : ℝ) :=
    Eventually.of_forall fun m => Eventually.of_forall fun t => by
      rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
      exact measureReal_le_one
  have hlim : ∀ᵐ t ∂ν, Tendsto (fun m => F (μs m) t) l (𝓝 (F μ t)) := by
    filter_upwards [ae_null_payoff_level (μ : Measure Ω) hf ν] with t ht
    exact level_probability_tendsto_of_continuousAt_ae hweak hc ht
  have hdct := tendsto_integral_filter_of_dominated_convergence (fun _ : ℝ => (1 : ℝ)) hF hFb
    (integrable_const (1 : ℝ)) hlim
  simpa only [← heq] using hdct

/-- Signed bounded payoffs need only be continuous almost everywhere for the
limit law. The same observable is evaluated under each approximating law. -/
theorem integral_tendsto_of_weak_ae_continuous_bounded [HasOuterApproxClosed Ω]
    {l : Filter Γ} [l.IsCountablyGenerated] {μs : Γ → ProbabilityMeasure Ω} {μ : ProbabilityMeasure Ω}
    (hweak : Tendsto μs l (𝓝 μ)) {f : Ω → ℝ} (hf : Measurable f) {H : ℝ}
    (hbound : ∀ x, |f x| ≤ H) (hc : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt f x) :
    Tendsto (fun m => ∫ x, f x ∂(μs m : Measure Ω)) l (𝓝 (∫ x, f x ∂(μ : Measure Ω))) := by
  have hg : ∀ x, f x + H ∈ Icc (0 : ℝ) (2 * H) := by
    intro x
    have hx := abs_le.mp (hbound x)
    constructor <;> linarith only [hx.1, hx.2]
  have hgc : ∀ᵐ x ∂(μ : Measure Ω), ContinuousAt (fun y => f y + H) x :=
    hc.mono fun _ hx => hx.add continuousAt_const
  have hi (P : ProbabilityMeasure Ω) : Integrable f (P : Measure Ω) := by
    apply Integrable.of_bound hf.aestronglyMeasurable H
    exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hbound x
  have hconv := integral_tendsto_of_weak_ae_continuous_range hweak (hf.add measurable_const) hg hgc
  have heq (P : ProbabilityMeasure Ω) : (∫ x, f x + H ∂(P : Measure Ω)) = (∫ x, f x ∂(P : Measure Ω)) + H := by
    rw [integral_add (hi P) (integrable_const H)]
    simp only [integral_const, probReal_univ, one_smul]
  change Tendsto (fun m => ∫ x, f x + H ∂(μs m : Measure Ω)) l
    (𝓝 (∫ x, f x + H ∂(μ : Measure Ω))) at hconv
  simp_rw [heq] at hconv
  simpa only [add_sub_cancel_right] using hconv.sub_const H

end ProphetSecretary.Probability
