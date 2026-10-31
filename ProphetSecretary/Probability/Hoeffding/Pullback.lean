import ProphetSecretary.Probability.Hoeffding.Orthogonality

/-!
# Pulling coordinate projections through actual independent samples

An injective coordinate query has exactly the corresponding product law.
Conditional averaging commutes with this query by a pathwise splicing
identity and its proved sampling law. This transports component centering to
the actual individual training coordinates used by empirical averages.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Probability.Hoeffding
variable {ι J : Type*} [Fintype ι] [Fintype J] [DecidableEq ι] [DecidableEq J]

def project {V : Type*} (e : ι ↪ J) (x : J → V) : ι → V := fun i => x (e i)

omit [DecidableEq ι] [DecidableEq J] in
lemma project_measurePreserving {V : Type*} [MeasurableSpace V] (μ : J → Measure V) [∀ j, IsProbabilityMeasure (μ j)] (e : ι ↪ J) :
    MeasurePreserving (project e) (Measure.pi μ) (Measure.pi (fun i => μ (e i))) := by
  have hi := iIndepFun.precomp e.injective
    (iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id))
  have hm := iIndepFun.map_fun_eq_pi_map (fun i => (measurable_pi_apply (e i)).aemeasurable) hi
  have he : (fun i => (Measure.pi μ).map (fun x => x (e i))) = fun i => μ (e i) := by
    funext i
    exact (measurePreserving_eval μ (e i)).map_eq
  change (Measure.pi μ).map (project e) = Measure.pi (fun i => (Measure.pi μ).map (fun x => x (e i))) at hm
  rw [he] at hm
  exact ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply (e i)),hm⟩

noncomputable def keptPreimage (e : ι ↪ J) (T : Finset J) : Finset ι := Finset.univ.filter (fun i => e i ∈ T)
noncomputable def liftSet (e : ι ↪ J) (A : Finset ι) : Finset J := A.map e

omit [Fintype J] in
lemma project_splice (e : ι ↪ J) (T : Finset J) (x y : J → ℝ) :
    project e (splice T x y) = splice (keptPreimage e T) (project e x) (project e y) := by
  funext i
  simp only [project,splice,keptPreimage,Finset.mem_filter,Finset.mem_univ,true_and]

omit [Fintype J] [DecidableEq ι] in
lemma liftSet_subset_iff (e : ι ↪ J) (A : Finset ι) (T : Finset J) :
    liftSet e A ⊆ T ↔ A ⊆ keptPreimage e T := by
  constructor
  · intro h i hi
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,h (Finset.mem_map.mpr ⟨i,hi,rfl⟩)⟩
  · intro h j hj
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact (Finset.mem_filter.mp (h hi)).2

omit [Fintype J] [DecidableEq ι] in
lemma keptPreimage_liftSet (e : ι ↪ J) (A : Finset ι) : keptPreimage e (liftSet e A) = A := by
  ext i
  simp only [keptPreimage,liftSet,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_map]
  constructor
  · rintro ⟨j,hj,he⟩
    exact (e.injective he) ▸ hj
  · intro hi
    exact ⟨i,hi,rfl⟩

lemma conditionalMean_pullback (μ : J → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (e : ι ↪ J) (T : Finset J) {f : (ι → ℝ) → ℝ} (hf : Measurable f) (x : J → ℝ) :
    conditionalMean μ T (fun y => f (project e y)) x =
      conditionalMean (fun i => μ (e i)) (keptPreimage e T) f (project e x) := by
  have hp := project_measurePreserving μ e
  have hfm : Measurable (fun y => f (splice (keptPreimage e T) (project e x) y)) :=
    hf.comp (measurable_splice_right _ _)
  have hi := integral_map (μ := Measure.pi μ) hp.measurable.aemeasurable hfm.aestronglyMeasurable
  rw [hp.map_eq] at hi
  unfold conditionalMean
  simp_rw [project_splice]
  exact hi.symm

lemma conditionalMean_liftedComponent (μ : J → Measure ℝ) [∀ j, IsProbabilityMeasure (μ j)]
    (e : ι ↪ J) (A : Finset ι) (T : Finset J) {f : (ι → ℝ) → ℝ}
    (hf : Measurable f) (C : ℝ≥0) (hb : ∀ x, |f x| ≤ C) (x : J → ℝ) :
    conditionalMean μ T (fun y => component (fun i => μ (e i)) A f (project e y)) x =
      if liftSet e A ⊆ T then component (fun i => μ (e i)) A f (project e x) else 0 := by
  rw [conditionalMean_pullback μ e T (measurable_component _ A hf),
    conditionalMean_component _ A (keptPreimage e T) hf C hb]
  by_cases hLift : liftSet e A ⊆ T
  · rw [if_pos hLift,if_pos ((liftSet_subset_iff e A T).mp hLift)]
  · rw [if_neg hLift,if_neg (fun h => hLift ((liftSet_subset_iff e A T).mpr h))]

omit [Fintype J] in
lemma liftedComponent_splice (μ : J → Measure ℝ) (e : ι ↪ J) (A : Finset ι)
    (f : (ι → ℝ) → ℝ) (x y : J → ℝ) :
    component (fun i => μ (e i)) A f (project e (splice (liftSet e A) x y)) =
      component (fun i => μ (e i)) A f (project e x) := by
  rw [project_splice,keptPreimage_liftSet,component_splice]

end ProphetSecretary.Probability.Hoeffding
