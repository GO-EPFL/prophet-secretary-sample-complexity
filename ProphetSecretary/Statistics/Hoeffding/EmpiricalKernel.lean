import ProphetSecretary.Statistics.Hoeffding.Sampling

/-!
# Actual product-empirical kernel expectations

The fixed kernel is integrated against independent empirical marginals.
Measurability, boundedness, exact mean preservation, finite linearity and AE
representative invariance are proved under the actual training product law.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.Hoeffding
open ProphetSecretary.Probability.Hoeffding ProphetSecretary.Model
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

omit [DecidableEq ι] [NeZero k] in
lemma measurable_empiricalMean_joint {f : (ι → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (fun z : (((ι × Fin k) → ℝ) × (ι → Fin k)) => f (project (sampleEmbedding z.2) z.1)) := by
  apply measurable_from_prod_countable_left
  intro a
  exact hf.comp (measurable_pi_lambda _ fun i => measurable_pi_apply (i,a i))

omit [DecidableEq ι] [NeZero k] in
lemma measurable_empiricalMean {f : (ι → ℝ) → ℝ} (hf : Measurable f) :
    Measurable (empiricalMean (k := k) f) :=
  ((measurable_empiricalMean_joint hf).stronglyMeasurable.integral_prod_right'
    (ν := Measure.pi (fun _ : ι => empiricalIndexLaw k))).measurable

omit [DecidableEq ι] in
lemma empiricalMean_abs_le {f : (ι → ℝ) → ℝ} {C : ℝ} (hb : ∀ x, |f x| ≤ C) (y : (ι × Fin k) → ℝ) :
    |empiricalMean f y| ≤ C := by
  have h := norm_integral_le_of_norm_le_const (μ := Measure.pi (fun _ : ι => empiricalIndexLaw k))
    (f := fun a => f (project (sampleEmbedding a) y))
    (Eventually.of_forall fun a => by simpa only [Real.norm_eq_abs] using hb (project (sampleEmbedding a) y))
  simpa only [empiricalMean,Real.norm_eq_abs,probReal_univ,mul_one] using h

omit [DecidableEq ι] in
lemma memLp_empiricalMean (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (p : ENNReal) :
    MemLp (empiricalMean (k := k) f) p (Measure.pi (fun q : ι × Fin k => μ q.1)) := by
  apply MemLp.of_bound (measurable_empiricalMean hf).aestronglyMeasurable C
  exact Eventually.of_forall fun y => by simpa only [Real.norm_eq_abs] using empiricalMean_abs_le hb y

omit [DecidableEq ι] in
lemma empiricalMean_const (c : ℝ) (y : (ι × Fin k) → ℝ) : empiricalMean (fun _ : ι → ℝ => c) y = c := by
  simp only [empiricalMean,integral_const,probReal_univ,one_smul]

omit [DecidableEq ι] in
lemma empiricalMean_finset_sum {J : Type*} (s : Finset J) (f : J → (ι → ℝ) → ℝ) (y : (ι × Fin k) → ℝ) :
    empiricalMean (fun x => ∑ j ∈ s, f j x) y = ∑ j ∈ s, empiricalMean (f j) y :=
  integral_finsetSum s (fun _ _ => Integrable.of_finite)

omit [DecidableEq ι] [NeZero k] in
lemma empiricalMean_congr_ae (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f g : (ι → ℝ) → ℝ} (hfg : f =ᵐ[Measure.pi μ] g) :
    empiricalMean (k := k) f =ᵐ[Measure.pi (fun q : ι × Fin k => μ q.1)] empiricalMean g := by
  have heach (a : ι → Fin k) := (sampleEmbedding_measurePreserving μ a).quasiMeasurePreserving.ae hfg
  filter_upwards [ae_all_iff.mpr heach] with y hy
  exact integral_congr_ae (Eventually.of_forall hy)

omit [DecidableEq ι] in
lemma integral_empiricalMean (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    (∫ y, empiricalMean (k := k) f y ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = ∫ x, f x ∂Measure.pi μ := by
  have hJI : Integrable (fun z : (((ι × Fin k) → ℝ) × (ι → Fin k)) => f (project (sampleEmbedding z.2) z.1))
      ((Measure.pi (fun q : ι × Fin k => μ q.1)).prod (Measure.pi (fun _ : ι => empiricalIndexLaw k))) := by
    apply Integrable.of_bound (measurable_empiricalMean_joint hf).aestronglyMeasurable C
    exact Eventually.of_forall fun z => by simpa only [Real.norm_eq_abs] using hb (project (sampleEmbedding z.2) z.1)
  have hi (a : ι → Fin k) :
      (∫ y, f (project (sampleEmbedding a) y) ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = ∫ x, f x ∂Measure.pi μ := by
    have hp := sampleEmbedding_measurePreserving μ a
    have h := integral_map (μ := Measure.pi (fun q : ι × Fin k => μ q.1)) hp.measurable.aemeasurable hf.aestronglyMeasurable
    rw [hp.map_eq] at h
    exact h.symm
  unfold empiricalMean
  rw [integral_integral_swap hJI]
  simp_rw [hi]
  simp only [integral_const,probReal_univ,one_smul]

lemma empiricalMean_sum_components (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (ι → ℝ) → ℝ) (y : (ι × Fin k) → ℝ) :
    empiricalMean f y = ∑ A ∈ (Finset.univ : Finset ι).powerset, empiricalMean (component μ A f) y := by
  calc
    _ = empiricalMean (fun x => ∑ A ∈ (Finset.univ : Finset ι).powerset, component μ A f x) y :=
      congrArg (fun g => empiricalMean g y) (funext fun x => (sum_components μ f x).symm)
    _ = _ := empiricalMean_finset_sum _ _ y

end ProphetSecretary.Statistics.Hoeffding
