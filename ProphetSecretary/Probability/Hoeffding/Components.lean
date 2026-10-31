import ProphetSecretary.Probability.Hoeffding.ConditionalMeanAlgebra
import ProphetSecretary.Probability.Hoeffding.SubsetDifference

/-!
# Constructed finite-product Hoeffding components

The component on A is the alternating subset difference of actual kept-
coordinate conditional means. Finite subset inversion reconstructs the kernel.
Each component depends only on its declared coordinates. Conditional averaging
onto T preserves it when A⊆T and annihilates it otherwise; this projection
identity is proved from product sampling and subset cancellation.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Probability.Hoeffding
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def component (μ : ι → Measure ℝ) (A : Finset ι) (f : (ι → ℝ) → ℝ) : (ι → ℝ) → ℝ :=
  subsetDifference (fun B => conditionalMean μ B f) A

lemma component_apply (μ : ι → Measure ℝ) (A : Finset ι) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    component μ A f x = ∑ B ∈ A.powerset, (-1 : ℝ)^(A.card-B.card)*conditionalMean μ B f x := by
  unfold component subsetDifference
  rw [Finset.sum_apply]
  apply Finset.sum_congr rfl
  intro B _
  rfl

lemma measurable_component (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (A : Finset ι)
    {f : (ι → ℝ) → ℝ} (hf : Measurable f) : Measurable (component μ A f) := by
  have he : component μ A f = fun x => ∑ B ∈ A.powerset, (-1 : ℝ)^(A.card-B.card)*conditionalMean μ B f x :=
    funext (component_apply μ A f)
  rw [he]
  exact Finset.measurable_sum _ (fun B _ => (measurable_conditionalMean μ hf).const_mul _)

lemma component_abs_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f : (ι → ℝ) → ℝ} (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (x : ι → ℝ) :
    |component μ A f x| ≤ (2 : ℝ)^A.card*C := by
  rw [component_apply]
  calc
    _ ≤ ∑ B ∈ A.powerset, |(-1 : ℝ)^(A.card-B.card)*conditionalMean μ B f x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _B ∈ A.powerset, (C : ℝ) := by
      apply Finset.sum_le_sum
      intro B _
      rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
      exact conditionalMean_abs_le μ B hb x
    _ = _ := by simp

lemma component_congr_on (μ : ι → Measure ℝ) (A : Finset ι) (f : (ι → ℝ) → ℝ)
    {x y : ι → ℝ} (hxy : ∀ i ∈ A, x i = y i) : component μ A f x = component μ A f y := by
  rw [component_apply,component_apply]
  apply Finset.sum_congr rfl
  intro B hB
  rw [conditionalMean_congr_on μ B f (fun i hi => hxy i (Finset.mem_powerset.mp hB hi))]

lemma component_splice (μ : ι → Measure ℝ) (A : Finset ι) (f : (ι → ℝ) → ℝ) (x y : ι → ℝ) :
    component μ A f (splice A x y) = component μ A f x := by
  apply component_congr_on μ A f
  intro i hi
  simp only [splice,if_pos hi]

lemma sum_components (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    (∑ A ∈ (Finset.univ : Finset ι).powerset, component μ A f x) = f x := by
  have h := congrFun (sum_subsetDifference (fun A => conditionalMean μ A f) (Finset.univ : Finset ι)) x
  change (∑ A ∈ (Finset.univ : Finset ι).powerset, component μ A f) x = conditionalMean μ Finset.univ f x at h
  rw [Finset.sum_apply,conditionalMean_univ] at h
  exact h

lemma component_empty (μ : ι → Measure ℝ) (f : (ι → ℝ) → ℝ) (x : ι → ℝ) :
    component μ ∅ f x = ∫ y, f y ∂Measure.pi μ := by
  unfold component
  rw [subsetDifference_empty,conditionalMean_empty]

lemma conditionalMean_component_apply (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A T : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0)
    (hb : ∀ x, |f x| ≤ C) (x : ι → ℝ) :
    conditionalMean μ T (component μ A f) x =
      ∑ B ∈ A.powerset, (-1 : ℝ)^(A.card-B.card)*conditionalMean μ (T ∩ B) f x := by
  have he : component μ A f = fun y => ∑ B ∈ A.powerset, (-1 : ℝ)^(A.card-B.card)*conditionalMean μ B f y :=
    funext (component_apply μ A f)
  rw [he,conditionalMean_finset_sum μ T A.powerset
    (fun B y => (-1 : ℝ)^(A.card-B.card)*conditionalMean μ B f y)
    (fun B _ => (measurable_conditionalMean μ hf).const_mul _) (fun _ => (C : ℝ))]
  · apply Finset.sum_congr rfl
    intro B _
    rw [conditionalMean_const_mul,conditionalMean_comp μ T B hf hb]
  · intro B _ y
    rw [abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul]
    exact conditionalMean_abs_le μ B hb y

/-- The actual coordinate conditional integrations are spectral projections on
the constructed components. No orthogonality is built into their definition. -/
theorem conditionalMean_component (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A T : Finset ι) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (C : ℝ≥0)
    (hb : ∀ x, |f x| ≤ C) (x : ι → ℝ) :
    conditionalMean μ T (component μ A f) x = if A ⊆ T then component μ A f x else 0 := by
  rw [conditionalMean_component_apply μ A T hf C hb]
  by_cases hAT : A ⊆ T
  · rw [if_pos hAT,component_apply]
    apply Finset.sum_congr rfl
    intro B hB
    rw [Finset.inter_eq_right.mpr ((Finset.mem_powerset.mp hB).trans hAT)]
  · rw [if_neg hAT]
    obtain ⟨i,hiA,hiT⟩ := Finset.not_subset.mp hAT
    have hz := subsetDifference_eq_zero_of_insert_invariant
      (fun B => conditionalMean μ (T ∩ B) f x) A hiA (fun B _ => by
        have he : T ∩ insert i B = T ∩ B := by
          ext j
          by_cases hji : j = i
          · subst j
            simp [hiT]
          · simp [hji]
        rw [he])
    simpa only [subsetDifference,smul_eq_mul] using hz

lemma component_congr_ae (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (A : Finset ι) {f g : (ι → ℝ) → ℝ} (hfg : f =ᵐ[Measure.pi μ] g) :
    component μ A f =ᵐ[Measure.pi μ] component μ A g := by
  have heach (B : A.powerset) : conditionalMean μ B f =ᵐ[Measure.pi μ] conditionalMean μ B g :=
    conditionalMean_congr_ae μ B hfg
  filter_upwards [ae_all_iff.mpr heach] with x hx
  rw [component_apply,component_apply]
  apply Finset.sum_congr rfl
  intro B hB
  rw [hx ⟨B,hB⟩]

end ProphetSecretary.Probability.Hoeffding
