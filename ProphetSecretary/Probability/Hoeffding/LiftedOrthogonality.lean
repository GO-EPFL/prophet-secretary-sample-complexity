import ProphetSecretary.Probability.Hoeffding.Pullback

/-!
# Orthogonality on distinct actual training-coordinate supports

A pulled component retains its proved coordinate projection identity on the
injected support. Two such components with different supports are orthogonal
under the actual larger product law, even when their source kernels or
coordinate queries differ. Sampling independence is never an input field.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Probability.Hoeffding
variable {ι κ J : Type*} [Fintype ι] [Fintype κ] [Fintype J]
  [DecidableEq ι] [DecidableEq κ] [DecidableEq J]

omit [DecidableEq J] in
lemma integral_lifted_component (μ : J → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (e : ι ↪ J) (A : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) :
    (∫ y, component (fun i => μ (e i)) A f (project e y) ∂Measure.pi μ) =
      ∫ x, component (fun i => μ (e i)) A f x ∂Measure.pi (fun i => μ (e i)) := by
  have hp := project_measurePreserving μ e
  have hi := integral_map (μ := Measure.pi μ) hp.measurable.aemeasurable
    (measurable_component (fun i => μ (e i)) A hf).aestronglyMeasurable
  rw [hp.map_eq] at hi
  exact hi.symm

omit [DecidableEq J] in
lemma variance_lifted_component (μ : J → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (e : ι ↪ J) (A : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) :
    variance (fun y => component (fun i => μ (e i)) A f (project e y)) (Measure.pi μ) =
      variance (component (fun i => μ (e i)) A f) (Measure.pi (fun i => μ (e i))) := by
  have hp := project_measurePreserving μ e
  have hi := variance_map (μ := Measure.pi μ) (Y := project e) (X := component (fun i => μ (e i)) A f)
    (by rw [hp.map_eq]; exact (measurable_component (fun i => μ (e i)) A hf).aemeasurable) hp.measurable.aemeasurable
  rw [hp.map_eq] at hi
  exact hi.symm

lemma integral_lifted_component_mul_eq_zero_of_not_subset
    (μ : J → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)] (e : ι ↪ J) (d : κ ↪ J)
    (A : Finset ι) (B : Finset κ) (hAB : ¬liftSet e A ⊆ liftSet d B)
    {f : (ι → ℝ) → ℝ} {g : (κ → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ≥0) (hfb : ∀ x, |f x| ≤ C) (hgb : ∀ x, |g x| ≤ D) :
    (∫ y, component (fun i => μ (e i)) A f (project e y)*
      component (fun i => μ (d i)) B g (project d y) ∂Measure.pi μ) = 0 := by
  have hfm := (measurable_component (fun i => μ (e i)) A hf).comp (project_measurePreserving μ e).measurable
  have hgm := (measurable_component (fun i => μ (d i)) B hg).comp (project_measurePreserving μ d).measurable
  have hp := integral_conditionalMean_mul μ (liftSet d B) hfm hgm
    ((2 : ℝ≥0)^A.card*C) ((2 : ℝ≥0)^B.card*D)
    (fun y => component_bound_nnreal (fun i => μ (e i)) A C hfb (project e y))
    (fun y => component_bound_nnreal (fun i => μ (d i)) B D hgb (project d y))
    (liftedComponent_splice μ d B g)
  simp only [Function.comp_def] at hp
  rw [← hp]
  have hz (y : J → ℝ) : conditionalMean μ (liftSet d B)
      (fun z => component (fun i => μ (e i)) A f (project e z)) y = 0 := by
    rw [conditionalMean_liftedComponent μ e A (liftSet d B) hf C hfb,if_neg hAB]
  simp_rw [hz,zero_mul]
  exact integral_zero _ _

/-- Different injected supports give actual zero cross moments. -/
theorem integral_lifted_component_mul_eq_zero
    (μ : J → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)] (e : ι ↪ J) (d : κ ↪ J)
    (A : Finset ι) (B : Finset κ) (hne : liftSet e A ≠ liftSet d B)
    {f : (ι → ℝ) → ℝ} {g : (κ → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ≥0) (hfb : ∀ x, |f x| ≤ C) (hgb : ∀ x, |g x| ≤ D) :
    (∫ y, component (fun i => μ (e i)) A f (project e y)*
      component (fun i => μ (d i)) B g (project d y) ∂Measure.pi μ) = 0 := by
  by_cases hAB : liftSet e A ⊆ liftSet d B
  · have hBA : ¬liftSet d B ⊆ liftSet e A := fun h => hne (Finset.Subset.antisymm hAB h)
    simpa only [mul_comm] using integral_lifted_component_mul_eq_zero_of_not_subset μ d e B A hBA hg hf D C hgb hfb
  · exact integral_lifted_component_mul_eq_zero_of_not_subset μ e d A B hAB hf hg C D hfb hgb

end ProphetSecretary.Probability.Hoeffding
