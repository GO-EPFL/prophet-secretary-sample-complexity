import ProphetSecretary.Statistics.Hoeffding.Decomposition
import ProphetSecretary.Probability.Hoeffding.FirstProjection

/-!
# First-order and higher-order empirical fluctuations

The first-order term is the actual average m^(-1)∑_{i,r}g_i(X_i^(r)).
Its summands are independent and centered. The remaining empirical Hoeffding
components have variance at most Var(f)/m², and hence at most 1/m² when the
fixed kernel satisfies |f|≤1. All constants are independent of instance size.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.Hoeffding
open ProphetSecretary.Probability.Hoeffding ProphetSecretary.Model
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

noncomputable def firstSubsets (ι : Type*) [Fintype ι] : Finset (Finset ι) :=
  (Finset.univ : Finset ι).powerset.filter (fun A => A.card = 1)
noncomputable def higherSubsets (ι : Type*) [Fintype ι] : Finset (Finset ι) :=
  (Finset.univ : Finset ι).powerset.filter (fun A => 2 ≤ A.card)
noncomputable def firstOrderEmpirical (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ)
    (y : (ι × Fin k) → ℝ) : ℝ := ∑ i : ι, empiricalMean (component μ {i} f) y
noncomputable def higherOrderEmpirical (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ)
    (y : (ι × Fin k) → ℝ) : ℝ := ∑ A ∈ higherSubsets ι, empiricalMean (component μ A f) y

lemma sum_firstSubsets {E : Type*} [AddCommMonoid E] (F : Finset ι → E) :
    (∑ A ∈ firstSubsets ι, F A) = ∑ i : ι, F {i} := by
  have he : firstSubsets ι = (Finset.univ : Finset ι).image (fun i => ({i} : Finset ι)) := by
    ext A
    simp only [firstSubsets,Finset.mem_filter,Finset.mem_powerset,Finset.subset_univ,true_and,Finset.mem_image]
    constructor
    · intro hA
      obtain ⟨i,hi⟩ := Finset.card_eq_one.mp hA
      exact ⟨i,Finset.mem_univ i,hi.symm⟩
    · rintro ⟨i,_,rfl⟩
      exact Finset.card_singleton i
  rw [he,Finset.sum_image]
  intro i _ j _ hij
  change ({i} : Finset ι) = {j} at hij
  have hi : i ∈ ({j} : Finset ι) := by rw [← hij]; exact Finset.mem_singleton_self i
  exact Finset.mem_singleton.mp hi

lemma nonemptySubsets_partition : nonemptySubsets ι = firstSubsets ι ∪ higherSubsets ι := by
  ext A
  simp only [nonemptySubsets,firstSubsets,higherSubsets,Finset.mem_filter,Finset.mem_union]
  constructor
  · rintro ⟨hA,hn⟩
    have hpos := Finset.card_pos.mpr hn
    by_cases h1 : A.card = 1
    · exact Or.inl ⟨hA,h1⟩
    · exact Or.inr ⟨hA,by omega⟩
  · rintro (⟨hA,h1⟩ | ⟨hA,h2⟩)
    · exact ⟨hA,Finset.card_pos.mp (by omega)⟩
    · exact ⟨hA,Finset.card_pos.mp (by omega)⟩

omit [DecidableEq ι] in
lemma first_higher_disjoint : Disjoint (firstSubsets ι) (higherSubsets ι) := by
  apply Finset.disjoint_left.mpr
  intro A h1 h2
  have h := (Finset.mem_filter.mp h1).2
  have h' := (Finset.mem_filter.mp h2).2
  omega

lemma empiricalMean_singleton (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (i : ι) (y : (ι × Fin k) → ℝ) :
    empiricalMean (component μ {i} f) y = (k : ℝ)⁻¹ * ∑ r : Fin k, firstProjection μ f i (y (i,r)) := by
  have hp := measurePreserving_eval (fun _ : ι => empiricalIndexLaw k) i
  let F : Fin k → ℝ := fun r => firstProjection μ f i (y (i,r))
  have hi := integral_map (μ := Measure.pi (fun _ : ι => empiricalIndexLaw k)) hp.measurable.aemeasurable
    (measurable_of_finite F).aestronglyMeasurable
  rw [hp.map_eq] at hi
  have heq : (fun a : ι → Fin k => component μ {i} f (project (sampleEmbedding a) y)) =
      fun a => F (a i) := by
    funext a
    exact (firstProjection_eq_component μ f i (project (sampleEmbedding a) y)).symm
  unfold empiricalMean
  rw [heq,← hi,integral_uniform_index]

/-- Exact first-order sample sum, with identities and sample indices explicit. -/
theorem firstOrderEmpirical_eq_sample_average (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (y : (ι × Fin k) → ℝ) :
    firstOrderEmpirical μ f y = (k : ℝ)⁻¹ * ∑ q : ι × Fin k, firstProjection μ f q.1 (y q) := by
  unfold firstOrderEmpirical
  simp_rw [empiricalMean_singleton]
  rw [← Finset.mul_sum,← Finset.univ_product_univ,Finset.sum_product]

omit [NeZero k] in
/-- Actual independent scaled first-order summands under the original product
training law, with no finite-support restriction on the offer laws. -/
theorem firstOrder_summands_independent (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) :
    iIndepFun (fun q : ι × Fin k => fun y : (ι × Fin k) → ℝ => (k : ℝ)⁻¹*firstProjection μ f q.1 (y q))
      (Measure.pi (fun q : ι × Fin k => μ q.1)) :=
  iIndepFun_pi (μ := fun q : ι × Fin k => μ q.1)
    (fun q => ((measurable_firstProjection μ hf q.1).const_mul _).aemeasurable)

omit [NeZero k] in
lemma firstOrder_summand_abs_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (q : ι × Fin k) (y : (ι × Fin k) → ℝ) :
    |(k : ℝ)⁻¹*firstProjection μ f q.1 (y q)| ≤ 2*(C : ℝ)/(k : ℝ) := by
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))]
  exact (mul_le_mul_of_nonneg_left (firstProjection_abs_le μ C hb q.1 (y q)) (by positivity)).trans_eq (by ring)

theorem empiricalMean_order_decomposition (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (ι → ℝ) → ℝ) (y : (ι × Fin k) → ℝ) :
    empiricalMean f y = (∫ x, f x ∂Measure.pi μ)+firstOrderEmpirical μ f y+higherOrderEmpirical μ f y := by
  have h := empiricalMean_centered_decomposition μ f y
  rw [nonemptySubsets_partition,Finset.sum_union first_higher_disjoint,sum_firstSubsets] at h
  change empiricalMean f y-(∫ x, f x ∂Measure.pi μ) = firstOrderEmpirical μ f y+higherOrderEmpirical μ f y at h
  linarith

theorem variance_firstOrderEmpirical (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance (firstOrderEmpirical (k := k) μ f) (Measure.pi (fun q : ι × Fin k => μ q.1)) =
      (k : ℝ)⁻¹ * ∑ i : ι, ∫ a, firstProjection μ f i a^2 ∂μ i := by
  have he : firstOrderEmpirical (k := k) μ f = fun y => ∑ A ∈ firstSubsets ι, empiricalMean (component μ A f) y := by
    funext y
    exact (sum_firstSubsets (fun A => empiricalMean (component μ A f) y)).symm
  rw [he,variance_empirical_component_sum μ (firstSubsets ι)
    (fun A hA => Finset.card_pos.mp (by have h := (Finset.mem_filter.mp hA).2; omega)) hf C hb,sum_firstSubsets]
  simp_rw [Finset.card_singleton,pow_one,← integral_sq_firstProjection μ hf C hb]
  rw [Finset.mul_sum]

omit [DecidableEq ι] in
lemma higherSubsets_nonempty (A : Finset ι) (hA : A ∈ higherSubsets ι) : A.Nonempty :=
  Finset.card_pos.mp (by have h := (Finset.mem_filter.mp hA).2; omega)

theorem variance_higherOrderEmpirical_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance (higherOrderEmpirical (k := k) μ f) (Measure.pi (fun q : ι × Fin k => μ q.1)) ≤
      ((k : ℝ)^2)⁻¹ * variance f (Measure.pi μ) := by
  have hk : 1 ≤ (k : ℝ) := by exact_mod_cast (NeZero.pos k)
  have hkinv0 : 0 ≤ (k : ℝ)⁻¹ := by positivity
  have hkinv1 : (k : ℝ)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ hk
  have hsub : higherSubsets ι ⊆ nonemptySubsets ι := by
    intro A hA
    exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hA).1,higherSubsets_nonempty A hA⟩
  have hSum : (∑ A ∈ higherSubsets ι, variance (component μ A f) (Measure.pi μ)) ≤ variance f (Measure.pi μ) := by
    rw [variance_eq_sum_nonempty_component_variances μ hf C hb]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun A _ _ => variance_nonneg _ _)
  unfold higherOrderEmpirical
  rw [variance_empirical_component_sum μ (higherSubsets ι) higherSubsets_nonempty hf C hb]
  calc
    _ ≤ ∑ A ∈ higherSubsets ι, ((k : ℝ)^2)⁻¹*variance (component μ A f) (Measure.pi μ) := by
      apply Finset.sum_le_sum
      intro A hA
      have hp := pow_le_pow_of_le_one hkinv0 hkinv1 (Finset.mem_filter.mp hA).2
      apply mul_le_mul_of_nonneg_right _ (variance_nonneg _ _)
      simpa only [inv_pow] using hp
    _ = ((k : ℝ)^2)⁻¹ * ∑ A ∈ higherSubsets ι, variance (component μ A f) (Measure.pi μ) := by rw [Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hSum (by positivity)

omit [DecidableEq ι] in
lemma variance_kernel_le_bound_sq (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance f (Measure.pi μ) ≤ (C : ℝ)^2 := by
  have hF2 : MemLp f 2 (Measure.pi μ) := MemLp.of_bound hf.aestronglyMeasurable C
    (Eventually.of_forall fun x => by simpa only [Real.norm_eq_abs] using hb x)
  apply (variance_le_expectation_sq hf.aestronglyMeasurable).trans
  have hle : (∫ x, f x^2 ∂Measure.pi μ) ≤ ∫ _x : ι → ℝ, (C : ℝ)^2 ∂Measure.pi μ := by
    apply integral_mono hF2.integrable_sq (integrable_const _)
    intro x
    have h := abs_le.mp (hb x)
    nlinarith
  simpa only [Pi.pow_apply,integral_const,probReal_univ,one_smul] using hle

/-- The source pilot's dimension-free higher-order second-moment scale. -/
theorem variance_higherOrderEmpirical_le_bound_sq (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance (higherOrderEmpirical (k := k) μ f) (Measure.pi (fun q : ι × Fin k => μ q.1)) ≤
      (C : ℝ)^2/(k : ℝ)^2 := by
  exact (variance_higherOrderEmpirical_le μ hf C hb).trans
    ((mul_le_mul_of_nonneg_left (variance_kernel_le_bound_sq μ hf C hb) (by positivity)).trans_eq (by ring))

theorem variance_higherOrderEmpirical_le_one (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (hb : ∀ x, |f x| ≤ 1) :
    variance (higherOrderEmpirical (k := k) μ f) (Measure.pi (fun q : ι × Fin k => μ q.1)) ≤ 1/(k : ℝ)^2 := by
  simpa only [NNReal.coe_one,one_pow] using variance_higherOrderEmpirical_le_bound_sq μ hf 1 hb

lemma integral_higherOrderEmpirical (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    (∫ y, higherOrderEmpirical (k := k) μ f y ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  have hI (A : Finset ι) : Integrable (empiricalMean (k := k) (component μ A f))
      (Measure.pi (fun q : ι × Fin k => μ q.1)) :=
    (memLp_empirical_component μ A hf C hb 2).integrable (by norm_num)
  unfold higherOrderEmpirical
  rw [integral_finsetSum (higherSubsets ι) (fun A _ => hI A)]
  apply Finset.sum_eq_zero
  intro A hA
  rw [integral_empiricalMean μ (measurable_component μ A hf) ((2 : ℝ≥0)^A.card*C) (component_bound_nnreal μ A C hb),
    integral_component_eq_zero μ A (higherSubsets_nonempty A hA) hf C hb]

omit [NeZero k] in
lemma firstOrder_summand_integral_zero (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (q : ι × Fin k) :
    (∫ y : (ι × Fin k) → ℝ, (k : ℝ)⁻¹*firstProjection μ f q.1 (y q)
      ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  have hp := measurePreserving_eval (fun q : ι × Fin k => μ q.1) q
  have hi := integral_map (μ := Measure.pi (fun q : ι × Fin k => μ q.1)) hp.measurable.aemeasurable
    (measurable_firstProjection μ hf q.1).aestronglyMeasurable
  rw [hp.map_eq] at hi
  rw [integral_const_mul,← hi,integral_firstProjection μ hf C hb q.1,mul_zero]

lemma covariance_first_higher_eq_zero (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    covariance (firstOrderEmpirical (k := k) μ f) (higherOrderEmpirical (k := k) μ f)
      (Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  unfold firstOrderEmpirical higherOrderEmpirical
  rw [covariance_fun_sum_fun_sum' (fun i _ => memLp_empirical_component μ {i} hf C hb 2)
    (fun A _ => memLp_empirical_component μ A hf C hb 2)]
  apply Finset.sum_eq_zero
  intro i _
  apply Finset.sum_eq_zero
  intro A hA
  have hne : ({i} : Finset ι) ≠ A := by
    intro he
    have h1 : A.card = 1 := by rw [← he]; exact Finset.card_singleton i
    have h2 := (Finset.mem_filter.mp hA).2
    omega
  exact covariance_empirical_components_eq_zero μ {i} A (Finset.singleton_nonempty i) hne hf C hb

end ProphetSecretary.Statistics.Hoeffding
