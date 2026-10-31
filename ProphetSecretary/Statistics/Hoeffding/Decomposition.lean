import ProphetSecretary.Statistics.Hoeffding.EmpiricalKernel
import ProphetSecretary.Statistics.Hoeffding.SampleMoments

/-!
# The exact product-empirical Hoeffding variance identity

Empirical averaging preserves the constructed decomposition, and its
nonconstant components remain orthogonal under the actual training law.
Their proved k^(-|A|) diagonal variances therefore sum exactly. This is the
identity used in `eq:bayes-maximum-variance` and in the pilot analysis.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.Hoeffding
open ProphetSecretary.Probability.Hoeffding
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

noncomputable def nonemptySubsets (ι : Type*) [Fintype ι] : Finset (Finset ι) :=
  (Finset.univ : Finset ι).powerset.filter (fun A => A.Nonempty)

lemma empiricalMean_empty_component (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (y : (ι × Fin k) → ℝ) :
    empiricalMean (component μ ∅ f) y = ∫ x, f x ∂Measure.pi μ := by
  have he : component μ ∅ f = fun _ => ∫ x, f x ∂Measure.pi μ := funext (component_empty μ f)
  rw [he,empiricalMean_const]

lemma empiricalMean_centered_decomposition (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (ι → ℝ) → ℝ) (y : (ι × Fin k) → ℝ) :
    empiricalMean f y-(∫ x, f x ∂Measure.pi μ) = ∑ A ∈ nonemptySubsets ι, empiricalMean (component μ A f) y := by
  have hsplit := Finset.sum_filter_add_sum_filter_not (Finset.univ : Finset ι).powerset
    (fun A => A.Nonempty) (fun A => empiricalMean (component μ A f) y)
  have hempty : (Finset.univ : Finset ι).powerset.filter (fun A => ¬A.Nonempty) = {∅} := by
    ext A
    simp [Finset.not_nonempty_iff_eq_empty]
  rw [hempty,Finset.sum_singleton,empiricalMean_empty_component,← empiricalMean_sum_components μ f y] at hsplit
  change (∑ A ∈ nonemptySubsets ι, empiricalMean (component μ A f) y)+(∫ x, f x ∂Measure.pi μ) = empiricalMean f y at hsplit
  linarith

lemma memLp_empirical_component (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (p : ENNReal) :
    MemLp (empiricalMean (k := k) (component μ A f)) p (Measure.pi (fun q : ι × Fin k => μ q.1)) :=
  memLp_empiricalMean μ (measurable_component μ A hf) ((2 : ℝ≥0)^A.card*C) (component_bound_nnreal μ A C hb) p

/-- Exact empirical variance for any finite family of nonempty components. -/
theorem variance_empirical_component_sum (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (s : Finset (Finset ι)) (hs : ∀ A ∈ s, A.Nonempty) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance (fun y => ∑ A ∈ s, empiricalMean (k := k) (component μ A f) y)
      (Measure.pi (fun q : ι × Fin k => μ q.1)) =
      ∑ A ∈ s, ((k : ℝ)^A.card)⁻¹ * variance (component μ A f) (Measure.pi μ) := by
  rw [variance_fun_sum' (fun A _ => memLp_empirical_component μ A hf C hb 2)]
  apply Finset.sum_congr rfl
  intro A hA
  rw [Finset.sum_eq_single_of_mem A hA]
  · exact (covariance_self (memLp_empirical_component μ A hf C hb 2).aemeasurable).trans
      (variance_empirical_component μ A (hs A hA) hf C hb)
  · intro B _ hBA
    exact covariance_empirical_components_eq_zero μ A B (hs A hA) hBA.symm hf C hb

/-- Exact product-empirical variance identity for arbitrary bounded measurable
kernels and nonidentical independent marginal laws. -/
theorem variance_empiricalMean (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance (empiricalMean (k := k) f) (Measure.pi (fun q : ι × Fin k => μ q.1)) =
      ∑ A ∈ nonemptySubsets ι, ((k : ℝ)^A.card)⁻¹ * variance (component μ A f) (Measure.pi μ) := by
  have hcenter : (fun y => empiricalMean (k := k) f y-(∫ x, f x ∂Measure.pi μ)) =
      fun y => ∑ A ∈ nonemptySubsets ι, empiricalMean (component μ A f) y :=
    funext (empiricalMean_centered_decomposition μ f)
  have hshift : variance (fun y => empiricalMean (k := k) f y-(∫ x, f x ∂Measure.pi μ))
      (Measure.pi (fun q : ι × Fin k => μ q.1)) = variance (empiricalMean (k := k) f) (Measure.pi (fun q : ι × Fin k => μ q.1)) := by
    simpa only [sub_eq_add_neg] using variance_add_const (measurable_empiricalMean hf).aestronglyMeasurable (-(∫ x, f x ∂Measure.pi μ))
  rw [← hshift,hcenter]
  exact variance_empirical_component_sum μ (nonemptySubsets ι) (fun A hA => (Finset.mem_filter.mp hA).2) hf C hb

end ProphetSecretary.Statistics.Hoeffding
