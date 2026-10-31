import ProphetSecretary.Statistics.Hoeffding.Sampling
import ProphetSecretary.Probability.Hoeffding.LiftedOrthogonality

/-!
# Exact empirical variance of constructed Hoeffding components

The k^|A| restricted selectors query distinct training-coordinate supports.
Their cross moments vanish by the actual lifted-component projection identity;
each diagonal variance is the original component variance. Consequently
empirical averaging divides that variance by k^|A|. Components on different
original coordinate sets remain orthogonal after empirical averaging.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.Hoeffding
open ProphetSecretary.Probability.Hoeffding
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

noncomputable def queriedComponent (μ : ι → Measure ℝ) (A : Finset ι)
    (f : (ι → ℝ) → ℝ) (a : A → Fin k) (y : (ι × Fin k) → ℝ) : ℝ :=
  component μ A f (project (setSampleEmbedding A a) y)

lemma memLp_queriedComponent (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0)
    (hb : ∀ x, |f x| ≤ C) (a : A → Fin k) (p : ENNReal) :
    MemLp (queriedComponent μ A f a) p (Measure.pi (fun q : ι × Fin k => μ q.1)) :=
  (memLp_component μ A hf C hb p).comp_measurePreserving
    (sampleEmbedding_measurePreserving μ (extendSelector A a))

lemma integral_queriedComponent (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) (hA : A.Nonempty) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0)
    (hb : ∀ x, |f x| ≤ C) (a : A → Fin k) :
    (∫ y, queriedComponent μ A f a y ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 :=
  (integral_lifted_component (fun q : ι × Fin k => μ q.1) (setSampleEmbedding A a) A hf).trans
    (integral_component_eq_zero μ A hA hf C hb)

lemma variance_queriedComponent (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (a : A → Fin k) :
    variance (queriedComponent μ A f a) (Measure.pi (fun q : ι × Fin k => μ q.1)) =
      variance (component μ A f) (Measure.pi μ) :=
  variance_lifted_component (fun q : ι × Fin k => μ q.1) (setSampleEmbedding A a) A hf

lemma covariance_queriedComponents_eq_zero (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Finset ι) (hA : A.Nonempty) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (a : A → Fin k) (b : B → Fin k)
    (hne : liftSet (setSampleEmbedding A a) A ≠ liftSet (setSampleEmbedding B b) B) :
    covariance (queriedComponent μ A f a) (queriedComponent μ B f b)
      (Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  have hprod := integral_lifted_component_mul_eq_zero (fun q : ι × Fin k => μ q.1)
    (setSampleEmbedding A a) (setSampleEmbedding B b) A B hne hf hf C C hb hb
  change (∫ y, queriedComponent μ A f a y*queriedComponent μ B f b y ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 at hprod
  rw [covariance_eq_sub (memLp_queriedComponent μ A hf C hb a 2) (memLp_queriedComponent μ B hf C hb b 2)]
  change (∫ y, queriedComponent μ A f a y*queriedComponent μ B f b y ∂Measure.pi (fun q : ι × Fin k => μ q.1))-
    (∫ y, queriedComponent μ A f a y ∂Measure.pi (fun q : ι × Fin k => μ q.1))*
    (∫ y, queriedComponent μ B f b y ∂Measure.pi (fun q : ι × Fin k => μ q.1)) = 0
  rw [hprod,integral_queriedComponent μ A hA hf C hb a,zero_mul,sub_zero]

/-- The exact k^(-|A|) variance factor is proved from actual independent
samples, including arbitrary atoms and k=1. -/
theorem variance_empirical_component (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) (hA : A.Nonempty) {f : (ι → ℝ) → ℝ} (hf : Measurable f)
    (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    variance (empiricalMean (k := k) (component μ A f)) (Measure.pi (fun q : ι × Fin k => μ q.1)) =
      ((k : ℝ)^A.card)⁻¹ * variance (component μ A f) (Measure.pi μ) := by
  let c : ℝ := ((k : ℝ)^A.card)⁻¹
  have he : empiricalMean (k := k) (component μ A f) = fun y => c*∑ a : A → Fin k, queriedComponent μ A f a y :=
    funext (empiricalMean_component μ A f)
  have hs : variance (fun y => ∑ a : A → Fin k, queriedComponent μ A f a y)
      (Measure.pi (fun q : ι × Fin k => μ q.1)) =
      (k : ℝ)^A.card * variance (component μ A f) (Measure.pi μ) := by
    rw [variance_fun_sum' (s := Finset.univ) (fun a _ => memLp_queriedComponent μ A hf C hb a 2)]
    calc
      _ = ∑ _a : A → Fin k, variance (component μ A f) (Measure.pi μ) := by
        apply Finset.sum_congr rfl
        intro a _
        rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ a)]
        · exact (covariance_self (memLp_queriedComponent μ A hf C hb a 2).aemeasurable).trans (variance_queriedComponent μ A hf a)
        · intro b _ hba
          exact covariance_queriedComponents_eq_zero μ A A hA hf C hb a b (setSampleLift_ne A hba.symm)
      _ = _ := by simp
  rw [he,variance_const_mul,hs]
  dsimp only [c]
  field_simp

theorem covariance_empirical_components_eq_zero (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A B : Finset ι) (hA : A.Nonempty) (hAB : A ≠ B) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) :
    covariance (empiricalMean (k := k) (component μ A f)) (empiricalMean (k := k) (component μ B f))
      (Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
  have heA : empiricalMean (k := k) (component μ A f) = fun y => ((k : ℝ)^A.card)⁻¹ *
      ∑ a : A → Fin k, queriedComponent μ A f a y := funext (empiricalMean_component μ A f)
  have heB : empiricalMean (k := k) (component μ B f) = fun y => ((k : ℝ)^B.card)⁻¹ *
      ∑ b : B → Fin k, queriedComponent μ B f b y := funext (empiricalMean_component μ B f)
  rw [heA,heB,covariance_const_mul_left,covariance_const_mul_right,
    covariance_fun_sum_fun_sum (fun a => memLp_queriedComponent μ A hf C hb a 2)
      (fun b => memLp_queriedComponent μ B hf C hb b 2)]
  have hz (a : A → Fin k) (b : B → Fin k) :
      covariance (queriedComponent μ A f a) (queriedComponent μ B f b)
        (Measure.pi (fun q : ι × Fin k => μ q.1)) = 0 := by
    apply covariance_queriedComponents_eq_zero μ A B hA hf C hb a b
    exact sampleLift_ne_of_sets_ne A B (extendSelector A a) (extendSelector B b) hAB
  simp_rw [hz]
  simp

end ProphetSecretary.Statistics.Hoeffding
