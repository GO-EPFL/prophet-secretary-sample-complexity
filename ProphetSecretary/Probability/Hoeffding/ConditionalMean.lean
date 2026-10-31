import ProphetSecretary.Probability.Hoeffding.Splice

/-!
# Actual conditional coordinate means on a finite product

The kept-coordinate mean integrates an independent complete vector over all
unkept coordinates. For bounded measurable kernels every section is
integrable. Composition of two such means keeps precisely the intersection
of the coordinate sets, by the proved independent splicing sampler.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Probability.Hoeffding
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def conditionalMean (μ : ι → Measure ℝ) (A : Finset ι)
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : ℝ := ∫ y, f (splice A x y) ∂Measure.pi μ

lemma measurable_conditionalMean (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] {A : Finset ι}
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) : Measurable (conditionalMean μ A f) :=
  ((hf.comp (measurable_splice A)).stronglyMeasurable.integral_prod_right' (ν := Measure.pi μ)).measurable

lemma conditionalMean_abs_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} {C : ℝ} (hb : ∀ x, |f x| ≤ C) (x : ι → ℝ) :
    |conditionalMean μ A f x| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi μ) (f := fun y => f (splice A x y))
    (Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using hb (splice A x y))
  simpa only [conditionalMean,Real.norm_eq_abs,probReal_univ,mul_one] using h

lemma conditionalMean_congr_on (μ : ι → Measure ℝ) (A : Finset ι) (f : (ι → ℝ) → ℝ)
    {x y : ι → ℝ} (hxy : ∀ i ∈ A, x i = y i) : conditionalMean μ A f x = conditionalMean μ A f y := by
  unfold conditionalMean
  simp_rw [splice_congr_on A hxy]

lemma conditionalMean_univ (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) : conditionalMean μ Finset.univ f x = f x := by
  unfold conditionalMean
  simp_rw [splice_univ]
  simp only [integral_const,probReal_univ,one_smul]

lemma conditionalMean_empty (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    conditionalMean μ ∅ f x = ∫ y, f y ∂Measure.pi μ := by
  unfold conditionalMean
  simp_rw [splice_empty]

lemma conditionalMean_comp (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) {C : ℝ}
    (hb : ∀ x, |f x| ≤ C) (x : ι → ℝ) :
    conditionalMean μ A (conditionalMean μ B f) x = conditionalMean μ (A ∩ B) f x := by
  have hfm : Measurable (fun y => f (splice (A ∩ B) x y)) := hf.comp (measurable_splice_right _ x)
  have hJm : Measurable (fun z : (ι → ℝ) × (ι → ℝ) => f (splice (A ∩ B) x (splice B z.1 z.2))) :=
    hfm.comp (measurable_splice B)
  have hJ : Integrable (fun z : (ι → ℝ) × (ι → ℝ) => f (splice (A ∩ B) x (splice B z.1 z.2)))
      ((Measure.pi μ).prod (Measure.pi μ)) := by
    apply Integrable.of_bound hJm.aestronglyMeasurable C
    exact Eventually.of_forall fun z => by
      simpa only [Real.norm_eq_abs] using hb (splice (A ∩ B) x (splice B z.1 z.2))
  have hp := splice_measurePreserving μ B
  have hi := integral_map (μ := (Measure.pi μ).prod (Measure.pi μ)) hp.measurable.aemeasurable hfm.aestronglyMeasurable
  rw [hp.map_eq] at hi
  unfold conditionalMean
  simp_rw [splice_comp]
  exact (integral_prod _ hJ).symm.trans hi.symm

/-- Null modifications of the original kernel give null modifications of every
actual coordinate conditional mean, including for kernels bounded only AE. -/
lemma conditionalMean_congr_ae (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f g : (ι → ℝ) → ℝ} (hfg : f =ᵐ[Measure.pi μ] g) :
    conditionalMean μ A f =ᵐ[Measure.pi μ] conditionalMean μ A g := by
  have hp := (splice_measurePreserving μ A).quasiMeasurePreserving.ae hfg
  have hsections := Measure.ae_ae_of_ae_prod hp
  filter_upwards [hsections] with x hx
  exact integral_congr_ae hx

end ProphetSecretary.Probability.Hoeffding
