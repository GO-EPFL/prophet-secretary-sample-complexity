import ProphetSecretary.Probability.Hoeffding.Components
import Mathlib.Probability.Moments.Variance

/-!
# Orthogonality and variance decomposition of actual Hoeffding components

Coordinate projection annihilates a component containing an unobserved
coordinate. The actual conditional integration identity then makes distinct
components orthogonal. Their means, second moments and variance decomposition
are derived here, rather than required as component data.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Probability.Hoeffding
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma component_bound_nnreal (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (x : ι → ℝ) :
    |component μ A f x| ≤ (((2 : ℝ≥0)^A.card*C : ℝ≥0) : ℝ) := by
  simpa using component_abs_le μ A C hb x

lemma memLp_component (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0)
    (hb : ∀ x, |f x| ≤ C) (p : ENNReal) : MemLp (component μ A f) p (Measure.pi μ) := by
  apply MemLp.of_bound (measurable_component μ A hf).aestronglyMeasurable ((2 : ℝ)^A.card*C)
  exact Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using component_abs_le μ A C hb x

lemma integral_component_eq_zero (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) (hA : A.Nonempty) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) : (∫ x, component μ A f x ∂Measure.pi μ) = 0 := by
  have hn : ¬A ⊆ ∅ := by
    obtain ⟨i,hi⟩ := hA
    exact fun h => Finset.notMem_empty i (h hi)
  have h := conditionalMean_component μ A ∅ hf C hb (fun _ => 0)
  rw [if_neg hn,conditionalMean_empty] at h
  exact h

lemma integral_component_mul_eq_zero_of_not_subset (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Finset ι) (hAB : ¬A ⊆ B) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    (∫ x, component μ A f x*component μ B f x ∂Measure.pi μ) = 0 := by
  have hi := integral_conditionalMean_mul μ B (measurable_component μ A hf) (measurable_component μ B hf)
    ((2 : ℝ≥0)^A.card*C) ((2 : ℝ≥0)^B.card*C)
    (component_bound_nnreal μ A C hb) (component_bound_nnreal μ B C hb) (component_splice μ B f)
  rw [← hi]
  have hz (x : ι → ℝ) : conditionalMean μ B (component μ A f) x = 0 := by
    rw [conditionalMean_component μ A B hf C hb,if_neg hAB]
  simp_rw [hz,zero_mul]
  exact integral_zero _ _

/-- Distinct components are orthogonal even though they need not be independent. -/
theorem integral_component_mul_eq_zero (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Finset ι) (hne : A ≠ B) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    (∫ x, component μ A f x*component μ B f x ∂Measure.pi μ) = 0 := by
  by_cases hAB : A ⊆ B
  · have hBA : ¬B ⊆ A := fun h => hne (Finset.Subset.antisymm hAB h)
    simpa only [mul_comm] using integral_component_mul_eq_zero_of_not_subset μ B A hBA hf C hb
  · exact integral_component_mul_eq_zero_of_not_subset μ A B hAB hf C hb

lemma covariance_component_eq_zero (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Finset ι) (hne : A ≠ B) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) : covariance (component μ A f) (component μ B f) (Measure.pi μ) = 0 := by
  rw [covariance_eq_sub (memLp_component μ A hf C hb 2) (memLp_component μ B hf C hb 2)]
  change (∫ x, component μ A f x*component μ B f x ∂Measure.pi μ)-
    (∫ x, component μ A f x ∂Measure.pi μ)*(∫ x, component μ B f x ∂Measure.pi μ) = 0
  rw [integral_component_mul_eq_zero μ A B hne hf C hb]
  by_cases hA : A = ∅
  · have hB : B.Nonempty := Finset.nonempty_iff_ne_empty.mpr (fun h => hne (hA.trans h.symm))
    rw [integral_component_eq_zero μ B hB hf C hb,mul_zero,sub_zero]
  · rw [integral_component_eq_zero μ A (Finset.nonempty_iff_ne_empty.mpr hA) hf C hb,zero_mul,sub_zero]

/-- Exact finite-product variance decomposition, before empirical averaging. -/
theorem variance_eq_sum_component_variances (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance f (Measure.pi μ) = ∑ A ∈ (Finset.univ : Finset ι).powerset, variance (component μ A f) (Measure.pi μ) := by
  let s := (Finset.univ : Finset ι).powerset
  have hsum : f = fun x => ∑ A ∈ s, component μ A f x := funext fun x => (sum_components μ f x).symm
  calc
    _ = variance (fun x => ∑ A ∈ s, component μ A f x) (Measure.pi μ) := congrArg (fun g => variance g (Measure.pi μ)) hsum
    _ = ∑ A ∈ s, ∑ B ∈ s, covariance (component μ A f) (component μ B f) (Measure.pi μ) :=
      variance_fun_sum' (fun A _ => memLp_component μ A hf C hb 2)
    _ = ∑ A ∈ s, variance (component μ A f) (Measure.pi μ) := by
      apply Finset.sum_congr rfl
      intro A hA
      rw [Finset.sum_eq_single_of_mem A hA]
      · exact covariance_self (memLp_component μ A hf C hb 2).aemeasurable
      · intro B _ hBA
        exact covariance_component_eq_zero μ A B hBA.symm hf C hb

lemma variance_component_empty (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (ι → ℝ) → ℝ) : variance (component μ ∅ f) (Measure.pi μ) = 0 := by
  have he : component μ ∅ f = fun _ => ∫ y, f y ∂Measure.pi μ := funext (component_empty μ f)
  rw [he,← covariance_self measurable_const.aemeasurable]
  exact covariance_const_left _

lemma variance_component_eq_integral_sq (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) (hA : A.Nonempty) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance (component μ A f) (Measure.pi μ) = ∫ x, component μ A f x^2 ∂Measure.pi μ := by
  rw [variance_eq_integral (measurable_component μ A hf).aemeasurable,
    integral_component_eq_zero μ A hA hf C hb]
  simp only [sub_zero]

/-- The zero-order component is constant, so the original variance is exactly
the sum over nonempty coordinate sets. -/
theorem variance_eq_sum_nonempty_component_variances (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance f (Measure.pi μ) = ∑ A ∈ (Finset.univ : Finset ι).powerset.filter (fun A => A.Nonempty),
      variance (component μ A f) (Measure.pi μ) := by
  rw [variance_eq_sum_component_variances μ hf C hb]
  symm
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hA : A.Nonempty
  · simp only [if_pos hA]
  · have he : A = ∅ := Finset.not_nonempty_iff_eq_empty.mp hA
    subst A
    rw [variance_component_empty]
    simp

end ProphetSecretary.Probability.Hoeffding
