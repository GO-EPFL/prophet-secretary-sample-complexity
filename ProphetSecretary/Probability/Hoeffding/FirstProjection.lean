import ProphetSecretary.Probability.Hoeffding.Orthogonality
import ProphetSecretary.Model.TrainingCoordinates

/-!
# Actual singleton conditional projections

The first projection is the conditional mean given one offer, minus the full
kernel mean. It is a measurable function of that offer alone, is centered,
and is bounded by twice the kernel bound. Evaluating these fixed functions at
the actual independent training coordinates gives independent summands.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Probability.Hoeffding
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

lemma component_singleton (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) :
    component μ {i} f x = conditionalMean μ {i} f x-(∫ y, f y ∂Measure.pi μ) := by
  have h := congrFun (subsetDifference_insert (fun A => conditionalMean μ A f) (∅ : Finset ι) (i := i) (by simp)) x
  simp only [Finset.insert_empty,subsetDifference_empty,Pi.sub_apply] at h
  change component μ {i} f x = conditionalMean μ {i} f x-conditionalMean μ ∅ f x at h
  rw [conditionalMean_empty] at h
  exact h

noncomputable def firstProjection (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (i : ι) (a : ℝ) : ℝ :=
  component μ {i} f (Function.update (fun _ => 0) i a)

lemma firstProjection_eq_component (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) :
    firstProjection μ f i (x i) = component μ {i} f x := by
  apply component_congr_on μ {i} f
  intro j hj
  have hji : j = i := Finset.mem_singleton.mp hj
  subst j
  simp only [Function.update_self]

lemma measurable_firstProjection (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (i : ι) : Measurable (firstProjection μ f i) := by
  have hm : Measurable (fun a : ℝ => Function.update (fun _ : ι => (0 : ℝ)) i a) := by
    apply measurable_pi_lambda
    intro j
    by_cases hji : j = i
    · subst j
      simp only [Function.update_self]
      exact measurable_id
    · simp only [Function.update_of_ne hji]
      exact measurable_const
  exact (measurable_component μ {i} hf).comp hm

lemma firstProjection_abs_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (i : ι) (a : ℝ) :
    |firstProjection μ f i a| ≤ 2*(C : ℝ) := by
  simpa only [firstProjection,Finset.card_singleton,pow_one] using component_abs_le μ {i} C hb (Function.update (fun _ => 0) i a)

lemma integral_firstProjection (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (i : ι) :
    (∫ a, firstProjection μ f i a ∂μ i) = 0 := by
  have hp := measurePreserving_eval μ i
  have hi := integral_map (μ := Measure.pi μ) hp.measurable.aemeasurable (measurable_firstProjection μ hf i).aestronglyMeasurable
  rw [hp.map_eq] at hi
  have heq : (fun x : ι → ℝ => firstProjection μ f i (x i)) = component μ {i} f :=
    funext (firstProjection_eq_component μ f i)
  rw [heq] at hi
  exact hi.trans (integral_component_eq_zero μ {i} (Finset.singleton_nonempty i) hf C hb)

lemma firstProjection_eq_conditionalMean (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (i : ι) (x : ι → ℝ) :
    firstProjection μ f i (x i) = conditionalMean μ {i} f x-(∫ y, f y ∂Measure.pi μ) := by
  rw [firstProjection_eq_component,component_singleton]

lemma integral_sq_firstProjection (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (i : ι) :
    (∫ a, firstProjection μ f i a^2 ∂μ i) = variance (component μ {i} f) (Measure.pi μ) := by
  have hp := measurePreserving_eval μ i
  have hi := integral_map (μ := Measure.pi μ) hp.measurable.aemeasurable
    ((measurable_firstProjection μ hf i).pow_const 2).aestronglyMeasurable
  rw [hp.map_eq] at hi
  change (∫ a, firstProjection μ f i a^2 ∂μ i) = ∫ x, firstProjection μ f i (x i)^2 ∂Measure.pi μ at hi
  simp_rw [firstProjection_eq_component] at hi
  exact hi.trans (variance_component_eq_integral_sq μ {i} (Finset.singleton_nonempty i) hf C hb).symm

/-- The conditional projection extracts exactly the corresponding squared
fluctuation from the full kernel. This is the first-projection score identity. -/
lemma integral_kernel_firstProjection (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (i : ι) :
    (∫ x, f x*firstProjection μ f i (x i) ∂Measure.pi μ) = ∫ a, firstProjection μ f i a^2 ∂μ i := by
  let g := component μ {i} f
  let m := ∫ y, f y ∂Measure.pi μ
  have hGi := memLp_component μ {i} hf C hb 2
  have hm0 : (∫ x, g x ∂Measure.pi μ) = 0 :=
    integral_component_eq_zero μ {i} (Finset.singleton_nonempty i) hf C hb
  have hpoint (x : ι → ℝ) : conditionalMean μ {i} f x = g x+m := by
    have h := component_singleton μ f i x
    change g x = conditionalMean μ {i} f x-m at h
    linarith
  have hfun : (fun x => conditionalMean μ {i} f x*g x) = fun x => g x^2+m*g x := by
    funext x
    rw [hpoint]
    ring
  have hp := integral_conditionalMean_mul μ {i} hf (measurable_component μ {i} hf)
    C ((2 : ℝ≥0)^({i} : Finset ι).card*C) hb (component_bound_nnreal μ {i} C hb) (component_splice μ {i} f)
  have hleft : (fun x => f x*firstProjection μ f i (x i)) = fun x => f x*g x := by
    funext x
    rw [firstProjection_eq_component]
  rw [hleft,integral_sq_firstProjection μ hf C hb i,variance_component_eq_integral_sq μ {i} (Finset.singleton_nonempty i) hf C hb]
  change (∫ x, f x*g x ∂Measure.pi μ) = ∫ x, g x^2 ∂Measure.pi μ
  rw [← hp,hfun,integral_add hGi.integrable_sq ((hGi.integrable (by norm_num)).const_mul m),
    integral_const_mul,hm0,mul_zero,add_zero]

/-- Independence is derived from every actual training coordinate, including
independent repetitions within the same marginal. The kernel is fixed before
these samples are drawn. -/
theorem training_firstProjections_independent {n k : ℕ} (P : Model.Instance n)
    {f : (Fin n → ℝ) → ℝ} (hf : Measurable f) :
    iIndepFun (fun q : Fin n × Fin k => fun y : (Fin n × Fin k) → ℝ => firstProjection P.law f q.1 (y q))
      (P.trainingCoordinateLaw k) :=
  iIndepFun_pi (μ := fun q : Fin n × Fin k => P.law q.1)
    (fun q => (measurable_firstProjection P.law hf q.1).aemeasurable)

end ProphetSecretary.Probability.Hoeffding
