import ProphetSecretary.Probability.Hoeffding.ConditionalMean

/-!
# Linearity and conditional integration for actual coordinate means

Global boundedness supplies every section's integrability. Multiplication by
a function of the kept coordinates commutes with conditional averaging under
the actual product law. This is the projection identity used to prove
orthogonality of the constructed Hoeffding components.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Probability.Hoeffding
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma conditionalMean_const_mul (μ : ι → Measure ℝ) (A : Finset ι) (f : (ι → ℝ) → ℝ)
    (c : ℝ) (x : ι → ℝ) :
    conditionalMean μ A (fun y => c*f y) x = c*conditionalMean μ A f x := integral_const_mul c _

lemma conditionalMean_finset_sum (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {J : Type*} (s : Finset J) (f : J → (ι → ℝ) → ℝ)
    (hf : ∀ j ∈ s, Measurable (f j)) (C : J → ℝ) (hb : ∀ j ∈ s, ∀ x, |f j x| ≤ C j) (x : ι → ℝ) :
    conditionalMean μ A (fun y => ∑ j ∈ s, f j y) x = ∑ j ∈ s, conditionalMean μ A (f j) x := by
  have hI (j : J) (hj : j ∈ s) : Integrable (fun y => f j (splice A x y)) (Measure.pi μ) := by
    apply Integrable.of_bound ((hf j hj).comp (measurable_splice_right A x)).aestronglyMeasurable (C j)
    exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs,Function.comp_def] using hb j hj (splice A x y)
  exact integral_finsetSum s hI

lemma conditionalMean_const (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) (c : ℝ) (x : ι → ℝ) : conditionalMean μ A (fun _ => c) x = c := by
  simp only [conditionalMean,integral_const,probReal_univ,one_smul]

lemma integral_conditionalMean_mul (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f g : (ι → ℝ) → ℝ} (hf : Measurable f) (hg : Measurable g)
    (C D : ℝ≥0) (hfb : ∀ x, |f x| ≤ C) (hgb : ∀ x, |g x| ≤ D)
    (hkeep : ∀ x y, g (splice A x y) = g x) :
    (∫ x, conditionalMean μ A f x*g x ∂Measure.pi μ) = ∫ x, f x*g x ∂Measure.pi μ := by
  have hJm : Measurable (fun z : (ι → ℝ) × (ι → ℝ) => f (splice A z.1 z.2)*g z.1) :=
    (hf.comp (measurable_splice A)).mul (hg.comp measurable_fst)
  have hJI : Integrable (fun z : (ι → ℝ) × (ι → ℝ) => f (splice A z.1 z.2)*g z.1)
      ((Measure.pi μ).prod (Measure.pi μ)) := by
    apply Integrable.of_bound hJm.aestronglyMeasurable ((C : ℝ)*D)
    exact Eventually.of_forall fun z => by
      rw [Real.norm_eq_abs,abs_mul]
      exact mul_le_mul (hfb _) (hgb _) (abs_nonneg _) C.coe_nonneg
  have hp := splice_measurePreserving μ A
  have hi := integral_map (μ := (Measure.pi μ).prod (Measure.pi μ)) hp.measurable.aemeasurable
    (hf.mul hg).aestronglyMeasurable
  rw [hp.map_eq] at hi
  calc
    _ = ∫ x, ∫ y, f (splice A x y)*g x ∂Measure.pi μ ∂Measure.pi μ := by
      apply integral_congr_ae
      exact Eventually.of_forall fun x => (integral_mul_const (g x) (fun y => f (splice A x y))).symm
    _ = ∫ z : (ι → ℝ) × (ι → ℝ), f (splice A z.1 z.2)*g z.1 ∂(Measure.pi μ).prod (Measure.pi μ) :=
      (integral_prod _ hJI).symm
    _ = ∫ z : (ι → ℝ) × (ι → ℝ), f (splice A z.1 z.2)*g (splice A z.1 z.2) ∂(Measure.pi μ).prod (Measure.pi μ) := by
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by dsimp only; rw [hkeep]
    _ = ∫ x, f x*g x ∂Measure.pi μ := hi.symm

lemma integral_conditionalMean (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    (∫ x, conditionalMean μ A f x ∂Measure.pi μ) = ∫ x, f x ∂Measure.pi μ := by
  simpa only [mul_one] using integral_conditionalMean_mul μ A (g := fun _ : ι → ℝ => (1 : ℝ)) hf measurable_const C 1 hb (fun _ => by simp) (fun _ _ => rfl)

end ProphetSecretary.Probability.Hoeffding
