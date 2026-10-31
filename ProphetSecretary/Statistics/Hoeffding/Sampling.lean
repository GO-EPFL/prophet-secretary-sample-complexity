import ProphetSecretary.Probability.Hoeffding.Pullback
import ProphetSecretary.Probability.Hoeffding.UniformSelectors
import Mathlib.Data.ZMod.Basic

/-!
# Actual sample queries and support sets for empirical Hoeffding components

One selector chooses one training draw from each distribution. Its coordinate
query is injective, so its output has exactly the original product law. A
component on A only depends on the selector restricted to A; averaging over
those k^|A| restrictions is the actual product-empirical component.
-/
open MeasureTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.Hoeffding
open ProphetSecretary.Probability.Hoeffding ProphetSecretary.Model
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {k : ℕ} [NeZero k]

noncomputable def sampleEmbedding (a : ι → Fin k) : ι ↪ (ι × Fin k) where
  toFun i := (i,a i)
  inj' _ _ h := congrArg Prod.fst h
noncomputable def extendSelector (A : Finset ι) (a : A → Fin k) (i : ι) : Fin k :=
  if hi : i ∈ A then a ⟨i,hi⟩ else 0
noncomputable def setSampleEmbedding (A : Finset ι) (a : A → Fin k) : ι ↪ (ι × Fin k) :=
  sampleEmbedding (extendSelector A a)

noncomputable def empiricalMean (f : (ι → ℝ) → ℝ) (y : (ι × Fin k) → ℝ) : ℝ :=
  ∫ a : ι → Fin k, f (project (sampleEmbedding a) y) ∂Measure.pi (fun _ : ι => empiricalIndexLaw k)

omit [DecidableEq ι] [NeZero k] in
lemma sampleEmbedding_measurePreserving (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (a : ι → Fin k) :
    MeasurePreserving (project (sampleEmbedding a))
      (Measure.pi (fun q : ι × Fin k => μ q.1)) (Measure.pi μ) :=
  project_measurePreserving (fun q : ι × Fin k => μ q.1) (sampleEmbedding a)

omit [Fintype ι] [NeZero k] in
lemma sampleLift_first_image (A : Finset ι) (a : ι → Fin k) :
    (liftSet (sampleEmbedding a) A).image Prod.fst = A := by
  ext i
  simp only [Finset.mem_image,liftSet,Finset.mem_map]
  constructor
  · rintro ⟨q,⟨j,hj,rfl⟩,he⟩
    change j = i at he
    exact he ▸ hj
  · intro hi
    exact ⟨(i,a i),⟨i,hi,rfl⟩,rfl⟩

omit [Fintype ι] [NeZero k] in
lemma sampleLift_ne_of_sets_ne (A B : Finset ι) (a b : ι → Fin k) (hAB : A ≠ B) :
    liftSet (sampleEmbedding a) A ≠ liftSet (sampleEmbedding b) B := by
  intro h
  have he := congrArg (fun s : Finset (ι × Fin k) => s.image Prod.fst) h
  rw [sampleLift_first_image,sampleLift_first_image] at he
  exact hAB he

omit [Fintype ι] [DecidableEq ι] [NeZero k] in
lemma sampleLift_eq_iff (A : Finset ι) (a b : ι → Fin k) :
    liftSet (sampleEmbedding a) A = liftSet (sampleEmbedding b) A ↔ ∀ i ∈ A, a i = b i := by
  constructor
  · intro h i hi
    have hm : (i,a i) ∈ liftSet (sampleEmbedding b) A := h ▸ Finset.mem_map.mpr ⟨i,hi,rfl⟩
    obtain ⟨j,_hj,he⟩ := Finset.mem_map.mp hm
    have hji : j = i := congrArg Prod.fst he
    subst j
    exact (congrArg Prod.snd he).symm
  · intro h
    ext q
    simp only [liftSet,Finset.mem_map]
    constructor
    · rintro ⟨i,hi,rfl⟩
      refine ⟨i,hi,?_⟩
      change (i,b i) = (i,a i)
      rw [h i hi]
    · rintro ⟨i,hi,rfl⟩
      refine ⟨i,hi,?_⟩
      change (i,a i) = (i,b i)
      rw [h i hi]

omit [Fintype ι] in
lemma setSampleLift_ne (A : Finset ι) {a b : A → Fin k} (hab : a ≠ b) :
    liftSet (setSampleEmbedding A a) A ≠ liftSet (setSampleEmbedding A b) A := by
  intro h
  apply hab
  funext i
  have he := (sampleLift_eq_iff A (extendSelector A a) (extendSelector A b)).mp h i i.property
  simpa only [extendSelector,dif_pos i.property] using he

omit [Fintype ι] in
lemma setSample_eq_on (A : Finset ι) (a : ι → Fin k) (i : ι) (hi : i ∈ A) :
    extendSelector A (fun j : A => a j) i = a i := by
  simp only [extendSelector,dif_pos hi]

/-- Exact normalized restricted-selector formula for the empirical component. -/
lemma empiricalMean_component (μ : ι → Measure ℝ) (A : Finset ι) (f : (ι → ℝ) → ℝ)
    (y : (ι × Fin k) → ℝ) :
    empiricalMean (component μ A f) y = ((k : ℝ)^A.card)⁻¹ *
      ∑ a : A → Fin k, component μ A f (project (setSampleEmbedding A a) y) := by
  let e : A ↪ ι := ⟨Subtype.val,Subtype.val_injective⟩
  have hp := project_measurePreserving (fun _ : ι => empiricalIndexLaw k) e
  let F : (A → Fin k) → ℝ := fun a => component μ A f (project (setSampleEmbedding A a) y)
  have hi := integral_map (μ := Measure.pi (fun _ : ι => empiricalIndexLaw k)) hp.measurable.aemeasurable
    (measurable_of_finite F).aestronglyMeasurable
  rw [hp.map_eq] at hi
  have heq (a : ι → Fin k) : component μ A f (project (sampleEmbedding a) y) = F (project e a) := by
    apply component_congr_on μ A f
    intro i hiA
    change y (i,a i) = y (i,extendSelector A (fun j : A => a j) i)
    rw [setSample_eq_on A a i hiA]
  unfold empiricalMean
  simp_rw [heq]
  rw [← hi,integral_uniform_selectors]
  simp only [F,Fintype.card_coe]
  congr 1
  apply Finset.sum_congr
  · ext a
    simp only [Finset.mem_univ]
  · intro a _
    rfl

end ProphetSecretary.Statistics.Hoeffding
