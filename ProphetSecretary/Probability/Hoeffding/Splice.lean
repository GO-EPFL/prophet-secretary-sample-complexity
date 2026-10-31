import ProphetSecretary.Model.Independence

/-!
# Independent-coordinate splicing for finite product laws

Keeping one set of coordinates from one independent offer vector and the
remaining coordinates from another preserves the actual product law. This
sampling identity supplies the conditional integrations in the Hoeffding
decomposition; no conditional independence is assumed as an interface.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Probability.Hoeffding
variable {ι : Type*} [DecidableEq ι]

def splice (A : Finset ι) (x y : ι → ℝ) : ι → ℝ := fun i => if i ∈ A then x i else y i

lemma measurable_splice (A : Finset ι) :
    Measurable (fun z : (ι → ℝ) × (ι → ℝ) => splice A z.1 z.2) := by
  apply measurable_pi_lambda
  intro i
  by_cases hi : i ∈ A
  · simpa only [splice,if_pos hi,Function.comp_def] using (measurable_pi_apply i).comp measurable_fst
  · simpa only [splice,if_neg hi,Function.comp_def] using (measurable_pi_apply i).comp measurable_snd

lemma measurable_splice_right (A : Finset ι) (x : ι → ℝ) : Measurable (splice A x) :=
  (measurable_splice A).comp (measurable_const.prodMk measurable_id)

lemma splice_comp (A B : Finset ι) (x y z : ι → ℝ) :
    splice B (splice A x y) z = splice (A ∩ B) x (splice B y z) := by
  funext i
  by_cases hiA : i ∈ A <;> by_cases hiB : i ∈ B <;> simp [splice,hiA,hiB]

lemma splice_congr_on (A : Finset ι) {x y : ι → ℝ} (hxy : ∀ i ∈ A, x i = y i) (z : ι → ℝ) :
    splice A x z = splice A y z := by
  funext i
  by_cases hi : i ∈ A
  · simp only [splice,if_pos hi,hxy i hi]
  · simp only [splice,if_neg hi]

lemma splice_univ [Fintype ι] (x y : ι → ℝ) : splice Finset.univ x y = x := by
  funext i
  simp [splice]
lemma splice_empty (x y : ι → ℝ) : splice ∅ x y = y := by
  funext i
  simp [splice]

lemma splice_measurePreserving [Fintype ι] (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)] (A : Finset ι) :
    MeasurePreserving (fun z : (ι → ℝ) × (ι → ℝ) => splice A z.1 z.2)
      ((Measure.pi μ).prod (Measure.pi μ)) (Measure.pi μ) := by
  have hpack := (measurePreserving_arrowProdEquivProdArrow ℝ ℝ ι μ μ).symm
    (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ ι)
  have heach (i : ι) : MeasurePreserving (fun z : ℝ × ℝ => if i ∈ A then z.1 else z.2)
      ((μ i).prod (μ i)) (μ i) := by
    by_cases hi : i ∈ A
    · simpa only [if_pos hi] using (measurePreserving_fst (μ := μ i) (ν := μ i))
    · simpa only [if_neg hi] using (measurePreserving_snd (μ := μ i) (ν := μ i))
  exact (measurePreserving_pi (fun i => (μ i).prod (μ i)) μ heach).comp hpack

end ProphetSecretary.Probability.Hoeffding
