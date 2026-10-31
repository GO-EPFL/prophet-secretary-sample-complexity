import ProphetSecretary.Statistics.Hoeffding.OrderSplit
import ProphetSecretary.Probability.Hoeffding.BoundedRepresentative

/-!
# Exact empirical ANOVA for kernels bounded on their actual law

Symmetric clipping supplies a globally bounded representative without
altering any original or empirical random variable almost surely. The exact
variance identity and the first/higher-order bounds thus apply to the actual
pilot kernel, with no hypothesis on impossible offer vectors.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.Hoeffding
open ProphetSecretary.Probability.Hoeffding
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

omit [NeZero k] in
lemma firstOrderEmpirical_congr_ae (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f g : (ι → ℝ) → ℝ} (hfg : f =ᵐ[Measure.pi μ] g) :
    firstOrderEmpirical (k := k) μ f =ᵐ[Measure.pi (fun q : ι × Fin k => μ q.1)] firstOrderEmpirical μ g := by
  have heach (i : ι) := empiricalMean_congr_ae (k := k) μ (component_congr_ae μ {i} hfg)
  filter_upwards [ae_all_iff.mpr heach] with y hy
  exact Finset.sum_congr rfl (fun i _ => hy i)

omit [NeZero k] in
lemma higherOrderEmpirical_congr_ae (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f g : (ι → ℝ) → ℝ} (hfg : f =ᵐ[Measure.pi μ] g) :
    higherOrderEmpirical (k := k) μ f =ᵐ[Measure.pi (fun q : ι × Fin k => μ q.1)] higherOrderEmpirical μ g := by
  have heach (A : higherSubsets ι) := empiricalMean_congr_ae (k := k) μ (component_congr_ae μ A hfg)
  filter_upwards [ae_all_iff.mpr heach] with y hy
  exact Finset.sum_congr rfl (fun A hA => hy ⟨A,hA⟩)

lemma memLp_component_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0)
    (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (p : ENNReal) : MemLp (component μ A f) p (Measure.pi μ) := by
  have he := component_congr_ae μ A (boundedRepresentative_ae_eq C hb)
  exact (memLp_congr_ae he).mp
    (memLp_component μ A (measurable_boundedRepresentative C hf) C (boundedRepresentative_abs_le C f) p)

lemma memLp_empirical_component_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0)
    (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (p : ENNReal) :
    MemLp (empiricalMean (k := k) (component μ A f)) p (Measure.pi (fun q : ι × Fin k => μ q.1)) := by
  have he := empiricalMean_congr_ae (k := k) μ (component_congr_ae μ A (boundedRepresentative_ae_eq C hb))
  exact (memLp_congr_ae he).mp
    (memLp_empirical_component μ A (measurable_boundedRepresentative C hf) C (boundedRepresentative_abs_le C f) p)

lemma memLp_firstOrderEmpirical_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (p : ENNReal) :
    MemLp (firstOrderEmpirical (k := k) μ f) p (Measure.pi (fun q : ι × Fin k => μ q.1)) :=
  memLp_finsetSum Finset.univ (fun i _ => memLp_empirical_component_of_ae_bounded μ {i} hf C hb p)

lemma memLp_higherOrderEmpirical_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (p : ENNReal) :
    MemLp (higherOrderEmpirical (k := k) μ f) p (Measure.pi (fun q : ι × Fin k => μ q.1)) :=
  memLp_finsetSum (higherSubsets ι) (fun A _ => memLp_empirical_component_of_ae_bounded μ A hf C hb p)

/-- Exact ANOVA identity under the actual, merely AE-bounded kernel. -/
theorem variance_empiricalMean_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    variance (empiricalMean (k := k) f) (Measure.pi (fun q : ι × Fin k => μ q.1)) =
      ∑ A ∈ nonemptySubsets ι, ((k : ℝ)^A.card)⁻¹ * variance (component μ A f) (Measure.pi μ) := by
  let g := boundedRepresentative C f
  have hgm : Measurable g := measurable_boundedRepresentative C hf
  have he : g =ᵐ[Measure.pi μ] f := boundedRepresentative_ae_eq C hb
  calc
    _ = variance (empiricalMean (k := k) g) (Measure.pi (fun q : ι × Fin k => μ q.1)) :=
      (variance_congr (empiricalMean_congr_ae μ he)).symm
    _ = ∑ A ∈ nonemptySubsets ι, ((k : ℝ)^A.card)⁻¹ * variance (component μ A g) (Measure.pi μ) :=
      variance_empiricalMean μ hgm C (boundedRepresentative_abs_le C f)
    _ = _ := Finset.sum_congr rfl (fun A _ => congrArg (fun v : ℝ => ((k : ℝ)^A.card)⁻¹*v)
      (variance_congr (component_congr_ae μ A he)))

/-- Actual first-order variance; the summands are the original conditional
projections, not a different clipped score supplied to the learner. -/
theorem variance_firstOrderEmpirical_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    variance (firstOrderEmpirical (k := k) μ f) (Measure.pi (fun q : ι × Fin k => μ q.1)) =
      (k : ℝ)⁻¹ * ∑ i : ι, ∫ a, firstProjection μ f i a^2 ∂μ i := by
  let g := boundedRepresentative C f
  have hgm : Measurable g := measurable_boundedRepresentative C hf
  have he : g =ᵐ[Measure.pi μ] f := boundedRepresentative_ae_eq C hb
  calc
    _ = variance (firstOrderEmpirical (k := k) μ g) (Measure.pi (fun q : ι × Fin k => μ q.1)) :=
      (variance_congr (firstOrderEmpirical_congr_ae μ he)).symm
    _ = (k : ℝ)⁻¹ * ∑ i : ι, ∫ a, firstProjection μ g i a^2 ∂μ i :=
      variance_firstOrderEmpirical μ hgm C (boundedRepresentative_abs_le C f)
    _ = _ := by
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      exact integral_congr_ae ((firstProjection_congr_ae μ hgm hf he i).mono fun a ha => congrArg (fun v : ℝ => v^2) ha)

theorem variance_higherOrderEmpirical_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    variance (higherOrderEmpirical (k := k) μ f) (Measure.pi (fun q : ι × Fin k => μ q.1)) ≤ (C : ℝ)^2/(k : ℝ)^2 := by
  let g := boundedRepresentative C f
  have he : g =ᵐ[Measure.pi μ] f := boundedRepresentative_ae_eq C hb
  rw [← variance_congr (higherOrderEmpirical_congr_ae (k := k) μ he)]
  exact variance_higherOrderEmpirical_le_bound_sq μ (measurable_boundedRepresentative C hf) C (boundedRepresentative_abs_le C f)

lemma integral_higherOrderEmpirical_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    (∫ y, higherOrderEmpirical (k := k) μ f y ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  have he := higherOrderEmpirical_congr_ae (k := k) μ (boundedRepresentative_ae_eq C hb)
  exact (integral_congr_ae he.symm).trans
    (integral_higherOrderEmpirical μ (measurable_boundedRepresentative C hf) C (boundedRepresentative_abs_le C f))

omit [NeZero k] in
lemma firstOrder_summand_abs_le_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (q : ι × Fin k) :
    ∀ᵐ y ∂Measure.pi (fun q : ι × Fin k => μ q.1), |(k : ℝ)⁻¹*firstProjection μ f q.1 (y q)| ≤ 2*(C : ℝ)/(k : ℝ) := by
  have h := (measurePreserving_eval (fun q : ι × Fin k => μ q.1) q).quasiMeasurePreserving.ae
    (firstProjection_abs_le_ae μ hf C hb q.1)
  filter_upwards [h] with y hy
  rw [abs_mul,abs_of_nonneg (inv_nonneg.mpr (Nat.cast_nonneg k))]
  exact (mul_le_mul_of_nonneg_left hy (by positivity)).trans_eq (by ring)

omit [NeZero k] in
lemma firstOrder_summand_integral_zero_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (q : ι × Fin k) :
    (∫ y : (ι × Fin k) → ℝ, (k : ℝ)⁻¹*firstProjection μ f q.1 (y q)
      ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  have hp := measurePreserving_eval (fun q : ι × Fin k => μ q.1) q
  have hi := integral_map (μ := Measure.pi (fun q : ι × Fin k => μ q.1)) hp.measurable.aemeasurable
    (measurable_firstProjection μ hf q.1).aestronglyMeasurable
  rw [hp.map_eq] at hi
  rw [integral_const_mul,← hi,integral_firstProjection_of_ae_bounded μ hf C hb q.1,mul_zero]

private lemma covariance_ae_congr {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
    {X Y Z T : Ω → ℝ} (hX : X =ᵐ[μ] Z) (hY : Y =ᵐ[μ] T) : covariance X Y μ = covariance Z T μ := by
  unfold covariance
  rw [integral_congr_ae hX,integral_congr_ae hY]
  apply integral_congr_ae
  filter_upwards [hX,hY] with x hx hy
  rw [hx,hy]

lemma covariance_empirical_components_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Finset ι) (hA : A.Nonempty) (hAB : A ≠ B) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    covariance (empiricalMean (k := k) (component μ A f)) (empiricalMean (k := k) (component μ B f))
      (Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  have he := boundedRepresentative_ae_eq C hb
  have hAeq := empiricalMean_congr_ae (k := k) μ (component_congr_ae μ A he)
  have hBeq := empiricalMean_congr_ae (k := k) μ (component_congr_ae μ B he)
  exact (covariance_ae_congr hAeq hBeq).symm.trans
    (covariance_empirical_components_eq_zero μ A B hA hAB (measurable_boundedRepresentative C hf) C (boundedRepresentative_abs_le C f))

lemma covariance_first_higher_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    covariance (firstOrderEmpirical (k := k) μ f) (higherOrderEmpirical (k := k) μ f)
      (Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  have he := boundedRepresentative_ae_eq C hb
  exact (covariance_ae_congr (firstOrderEmpirical_congr_ae (k := k) μ he)
    (higherOrderEmpirical_congr_ae (k := k) μ he)).symm.trans
    (covariance_first_higher_eq_zero μ (measurable_boundedRepresentative C hf) C (boundedRepresentative_abs_le C f))

lemma variance_original_of_ae_bounded (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    variance f (Measure.pi μ) = ∑ A ∈ nonemptySubsets ι, variance (component μ A f) (Measure.pi μ) := by
  have he := boundedRepresentative_ae_eq C hb
  calc
    _ = variance (boundedRepresentative C f) (Measure.pi μ) := (variance_congr he).symm
    _ = ∑ A ∈ nonemptySubsets ι, variance (component μ A (boundedRepresentative C f)) (Measure.pi μ) :=
      variance_eq_sum_nonempty_component_variances μ (measurable_boundedRepresentative C hf) C (boundedRepresentative_abs_le C f)
    _ = _ := Finset.sum_congr rfl (fun A _ => variance_congr (component_congr_ae μ A he))

/-- The literal remainder after the paper's independent first-order sample sum. -/
noncomputable def empiricalRemainder (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (y : (ι × Fin k) → ℝ) : ℝ :=
  empiricalMean f y-(∫ x, f x ∂Measure.pi μ)-(k : ℝ)⁻¹*∑ q : ι × Fin k, firstProjection μ f q.1 (y q)

lemma empiricalRemainder_eq_higherOrder (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (ι → ℝ) → ℝ) : empiricalRemainder (k := k) μ f = higherOrderEmpirical μ f := by
  funext y
  have h := empiricalMean_order_decomposition μ f y
  rw [firstOrderEmpirical_eq_sample_average] at h
  change empiricalMean f y-(∫ x, f x ∂Measure.pi μ)-(k : ℝ)⁻¹*∑ q : ι × Fin k, firstProjection μ f q.1 (y q) = _
  linarith

lemma memLp_empiricalRemainder (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) (p : ENNReal) :
    MemLp (empiricalRemainder (k := k) μ f) p (Measure.pi (fun q : ι × Fin k => μ q.1)) := by
  rw [empiricalRemainder_eq_higherOrder]
  exact memLp_higherOrderEmpirical_of_ae_bounded μ hf C hb p

lemma integral_empiricalRemainder (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    (∫ y, empiricalRemainder (k := k) μ f y ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  rw [empiricalRemainder_eq_higherOrder]
  exact integral_higherOrderEmpirical_of_ae_bounded μ hf C hb

/-- The source pilot's bound for its literal higher-order remainder, without a
bound on impossible offer vectors. For C=1 the right-hand side is exactly 1/k². -/
theorem variance_empiricalRemainder_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    variance (empiricalRemainder (k := k) μ f) (Measure.pi (fun q : ι × Fin k => μ q.1)) ≤ (C : ℝ)^2/(k : ℝ)^2 := by
  rw [empiricalRemainder_eq_higherOrder]
  exact variance_higherOrderEmpirical_of_ae_bounded μ hf C hb

/-- Exact variance of the original independent first-order sample sum. -/
theorem variance_firstOrder_sample_sum (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0) (hb : ∀ᵐ x ∂Measure.pi μ, |f x| ≤ C) :
    variance (fun y : (ι × Fin k) → ℝ => (k : ℝ)⁻¹*∑ q : ι × Fin k, firstProjection μ f q.1 (y q))
      (Measure.pi (fun q : ι × Fin k => μ q.1)) = (k : ℝ)⁻¹*∑ i : ι, ∫ a, firstProjection μ f i a^2 ∂μ i := by
  have he := funext (firstOrderEmpirical_eq_sample_average (k := k) μ f)
  rw [← he]
  exact variance_firstOrderEmpirical_of_ae_bounded μ hf C hb

end ProphetSecretary.Statistics.Hoeffding
