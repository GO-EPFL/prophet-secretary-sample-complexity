import ProphetSecretary.Statistics.PlannerConditionalTransition
import ProphetSecretary.Statistics.PlannerTransitionDensity
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
# The complete seed law of the direct scalar-planner transition

The sampler first draws its nonempty subset, chooses one of its identities
uniformly, and then uses independent uniforms for the remaining-time maximum
and the additional subset inclusions.
-/

open MeasureTheory Set Filter
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

private lemma sum_three_restrict {X Y Z R : Type*} [Fintype X] [Fintype Y] [Fintype Z]
    [AddCommMonoid R] (S : Finset X) (T : X → Finset Y) (U : X → Y → Finset Z)
    (f : X → Y → Z → R) :
    (∑ x, ∑ y, ∑ z, if x ∈ S ∧ y ∈ T x ∧ z ∈ U x y then f x y z else 0) =
      ∑ x ∈ S, ∑ y ∈ T x, ∑ z ∈ U x y, f x y z := by
  calc
    (∑ x, ∑ y, ∑ z, if x ∈ S ∧ y ∈ T x ∧ z ∈ U x y then f x y z else 0) =
      ∑ x, if x ∈ S then
        (∑ y, if y ∈ T x then (∑ z, if z ∈ U x y then f x y z else 0) else 0) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ S
      · simp only [hx, true_and, ite_true]
        apply Finset.sum_congr rfl
        intro y _
        by_cases hy : y ∈ T x <;> simp [hy]
      · simp [hx]
    _ = _ := by simp only [Finset.sum_ite_mem_eq]

noncomputable instance plannerSamplerIndexFintype {n : ℕ} (A : Finset (Fin n)) :
    Fintype (PlannerSamplerIndex A) := by
  unfold PlannerSamplerIndex
  infer_instance

noncomputable instance plannerDensityIndexFintype {n : ℕ} (A : Finset (Fin n)) :
    Fintype (PlannerDensityIndex A) := by
  unfold PlannerDensityIndex
  infer_instance

lemma sum_plannerSamplerIndex {n : ℕ} {R : Type*} [AddCommMonoid R]
    (A : Finset (Fin n)) (f : Finset (Fin n) → Fin n → Finset (Fin n) → R) :
    (∑ z : PlannerSamplerIndex A, f z.1.1 z.1.2.1 z.1.2.2) =
      ∑ D ∈ A.powerset.erase ∅, ∑ i ∈ D, ∑ T ∈ (A \ D).powerset, f D i T := by
  let P : Finset (Fin n) × Fin n × Finset (Fin n) → Prop :=
    fun z => z.1 ⊆ A ∧ z.2.1 ∈ z.1 ∧ z.2.2 ⊆ A \ z.1
  have hIndex : (∑ z : PlannerSamplerIndex A, f z.1.1 z.1.2.1 z.1.2.2) =
      ∑ D, ∑ i, ∑ T, if D ⊆ A ∧ i ∈ D ∧ T ⊆ A \ D then f D i T else 0 := by
    change (∑ z : {z // P z}, f z.1.1 z.1.2.1 z.1.2.2) = _
    rw [← Finset.sum_subtype (Finset.univ.filter P) (fun z => by simp)
      (fun z => f z.1 z.2.1 z.2.2)]
    simp only [Finset.sum_filter, Fintype.sum_prod_type]
    rfl
  rw [hIndex]
  have hNested := sum_three_restrict A.powerset (fun D => D)
    (fun D _ => (A \ D).powerset) f
  simp only [Finset.mem_powerset] at hNested
  rw [hNested]
  have hErase := Finset.sum_erase_add A.powerset
    (fun D => ∑ i ∈ D, ∑ T ∈ (A \ D).powerset, f D i T) (Finset.empty_mem_powerset A)
  simpa using hErase.symm

lemma sum_plannerDensityIndex {n : ℕ} {R : Type*} [AddCommMonoid R]
    (A : Finset (Fin n)) (f : Fin n → Finset (Fin n) → Finset (Fin n) → R) :
    (∑ z : PlannerDensityIndex A, f z.1.1 z.1.2.1 z.1.2.2) =
      ∑ i ∈ A, ∑ B ∈ (A.erase i).powerset, ∑ C ∈ B.powerset, f i B C := by
  let P : Fin n × Finset (Fin n) × Finset (Fin n) → Prop :=
    fun z => z.1 ∈ A ∧ z.2.1 ⊆ A.erase z.1 ∧ z.2.2 ⊆ z.2.1
  change (∑ z : {z // P z}, f z.1.1 z.1.2.1 z.1.2.2) = _
  rw [← Finset.sum_subtype (Finset.univ.filter P) (fun z => by simp)
    (fun z => f z.1 z.2.1 z.2.2)]
  simp only [Finset.sum_filter, Fintype.sum_prod_type]
  have h := sum_three_restrict A (fun i => (A.erase i).powerset)
    (fun _ B => B.powerset) f
  simpa only [Finset.mem_powerset] using h

lemma lintegral_plannerNonemptySubsetPMF {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) (g : Finset (Fin n) → ℝ≥0∞) :
    (∫⁻ D, g D ∂(plannerNonemptySubsetPMF A p hA hp).toMeasure) =
      ∑ D ∈ A.powerset.erase ∅,
        ENNReal.ofReal ((∏ i ∈ D, (4 * p i)) / (plannerWeight A p - 1)) * g D := by
  rw [lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    plannerNonemptySubsetPMF_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro D _
  exact mul_comm _ _

lemma plannerNonemptySubsetPMF_ae_nonempty {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    ∀ᵐ D ∂(plannerNonemptySubsetPMF A p hA hp).toMeasure, D.Nonempty := by
  rw [ae_iff]
  have he : {D : Finset (Fin n) | ¬ D.Nonempty} = {∅} := by
    ext D
    simp
  rw [he, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    plannerNonemptySubsetPMF_apply]
  simp

lemma lintegral_uniformOfFinset {n : ℕ} (D : Finset (Fin n)) (hD : D.Nonempty)
    (g : Fin n → ℝ≥0∞) :
    (∫⁻ i, g i ∂(PMF.uniformOfFinset D hD).toMeasure) =
      ∑ i ∈ D, ENNReal.ofReal (1 / (D.card : ℝ)) * g i := by
  rw [lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    PMF.uniformOfFinset_apply, mul_ite, mul_zero]
  rw [Finset.sum_ite_mem]
  simp only [Finset.univ_inter]
  have hc : 0 < (D.card : ℝ) := Nat.cast_pos.mpr (Finset.card_pos.mpr hD)
  rw [one_div, ENNReal.ofReal_inv_of_pos hc, ENNReal.ofReal_natCast]
  apply Finset.sum_congr rfl
  intro i _
  exact mul_comm _ _

/-- Conditional on `D`, choose the identity uniformly before drawing the
independent continuous seeds. The empty branch has zero measure. -/
noncomputable def plannerIdentityTransitionLaw {n : ℕ} (A D : Finset (Fin n)) :
    Measure (Fin n × ℝ × Finset (Fin n)) :=
  if hD : D.Nonempty then (PMF.uniformOfFinset D hD).toMeasure.bind
    (fun i => plannerConditionalTransitionLaw A D hD i) else 0

lemma plannerIdentityTransitionLaw_probability {n : ℕ} (A D : Finset (Fin n))
    (hD : D.Nonempty) : IsProbabilityMeasure (plannerIdentityTransitionLaw A D) := by
  rw [plannerIdentityTransitionLaw, dif_pos hD]
  exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall (fun _ => inferInstance))

lemma lintegral_plannerIdentityTransitionLaw {n : ℕ} (A D : Finset (Fin n))
    (hD : D.Nonempty) (f : Fin n × ℝ × Finset (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂plannerIdentityTransitionLaw A D) =
      ∑ i ∈ D, ENNReal.ofReal (1 / (D.card : ℝ)) *
        ∫⁻ x, f x ∂plannerConditionalTransitionLaw A D hD i := by
  rw [plannerIdentityTransitionLaw, dif_pos hD,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable hf.aemeasurable,
    lintegral_uniformOfFinset]

/-- Actual distribution of all three coordinates produced by the sampler. -/
noncomputable def plannerTransitionLaw {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    Measure (Fin n × ℝ × Finset (Fin n)) :=
  (plannerNonemptySubsetPMF A p hA hp).toMeasure.bind (plannerIdentityTransitionLaw A)

instance plannerTransitionLaw_probability {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    IsProbabilityMeasure (plannerTransitionLaw A p hA hp) := by
  apply isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
  filter_upwards [plannerNonemptySubsetPMF_ae_nonempty A p hA hp] with D hD
  exact plannerIdentityTransitionLaw_probability A D hD

lemma lintegral_plannerTransitionLaw {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i)
    (f : Fin n × ℝ × Finset (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂plannerTransitionLaw A p hA hp) =
      ∑ D ∈ A.powerset.erase ∅,
        ENNReal.ofReal ((∏ i ∈ D, (4 * p i)) / (plannerWeight A p - 1)) *
          ∫⁻ x, f x ∂plannerIdentityTransitionLaw A D := by
  rw [plannerTransitionLaw,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable hf.aemeasurable,
    lintegral_plannerNonemptySubsetPMF]

/-- The measure specified by the planner kernel density. -/
noncomputable def plannerKernelLaw {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ) :
    Measure (Fin n × ℝ × Finset (Fin n)) :=
  ∑ i ∈ A, ∑ B ∈ (A.erase i).powerset,
    (Instance.uniformClock.withDensity (fun s => ENNReal.ofReal (plannerKernelDensity A p i B s))).map
      (fun s => (i, s, B))

lemma lintegral_plannerKernelLaw {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (f : Fin n × ℝ × Finset (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂plannerKernelLaw A p) =
      ∑ i ∈ A, ∑ B ∈ (A.erase i).powerset,
        ∫⁻ s, ENNReal.ofReal (plannerKernelDensity A p i B s) * f (i, s, B)
          ∂Instance.uniformClock := by
  rw [plannerKernelLaw, lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_finsetSum_measure]
  apply Finset.sum_congr rfl
  intro B _
  have hmap : Measurable (fun s : ℝ => (i, s, B)) :=
    measurable_const.prodMk (measurable_id.prodMk measurable_const)
  rw [lintegral_map hf hmap]
  exact lintegral_withDensity_eq_lintegral_mul _
    (by unfold plannerKernelDensity; fun_prop)
    (hf.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))

/-- Joint density of one branch before collecting equal output triples. -/
noncomputable def plannerJointDensity {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (D : Finset (Fin n)) (_i : Fin n) (T : Finset (Fin n)) (s : ℝ) : ℝ :=
  ((∏ j ∈ D, (4 * p j)) / (plannerWeight A p - 1)) *
    ((1 / (D.card : ℝ)) * ((D.card : ℝ) * s ^ (D.card - 1))) *
    s ^ T.card * (1 - s) ^ ((A \ D).card - T.card)

lemma plannerJointDensity_nonneg {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) {D : Finset (Fin n)} (hD : D ⊆ A)
    (i : Fin n) (T : Finset (Fin n)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ plannerJointDensity A p D i T s := by
  have hw := plannerNonemptySubset_weight_nonneg A p hp hD
  have hs0 := hs.1
  have hs1 := sub_nonneg.mpr hs.2
  unfold plannerJointDensity
  positivity

lemma plannerJointDensity_reindex {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (z : PlannerSamplerIndex A) (s : ℝ) :
    plannerJointDensity A p z.1.1 z.1.2.1 z.1.2.2 s =
      plannerTransitionContribution A p z.1.2.1
        (z.1.1.erase z.1.2.1 ∪ z.1.2.2) (z.1.1.erase z.1.2.1) s := by
  rcases z with ⟨⟨D, i, T⟩, hD, hi, hT⟩
  change D ⊆ A at hD
  change i ∈ D at hi
  change T ⊆ A \ D at hT
  have hDis : Disjoint (D.erase i) T := by
    apply Finset.disjoint_left.mpr
    intro j hjC hjT
    exact (Finset.mem_sdiff.mp (hT hjT)).2 (Finset.mem_erase.mp hjC).2
  have hCcard := Finset.card_erase_of_mem hi
  have hAcard := Finset.card_erase_of_mem (hD hi)
  have hUnion := Finset.card_union_of_disjoint hDis
  have hTail := Finset.card_sdiff_of_subset hD
  have hTcard := Finset.card_le_card hT
  have hDcard : 0 < D.card := Finset.card_pos.mpr ⟨i, hi⟩
  have hDAcard := Finset.card_le_card hD
  have hCD : (D.erase i).card + 1 = D.card := by omega
  have hBC : (D.erase i ∪ T).card - (D.erase i).card = T.card := by omega
  have hRest : (A.erase i).card - (D.erase i ∪ T).card = (A \ D).card - T.card := by omega
  change plannerJointDensity A p D i T s =
    plannerTransitionContribution A p i (D.erase i ∪ T) (D.erase i) s
  unfold plannerJointDensity plannerTransitionContribution
  rw [Finset.insert_erase hi, hCD, hBC, hRest, hCcard]

lemma plannerTransitionContribution_nonneg {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) {i : Fin n} (hi : i ∈ A)
    (B : Finset (Fin n)) {C : Finset (Fin n)} (hC : C ⊆ A)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    0 ≤ plannerTransitionContribution A p i B C s := by
  have hw := plannerNonemptySubset_weight_nonneg A p hp (Finset.insert_subset_iff.mpr ⟨hi, hC⟩)
  have hs0 := hs.1
  have hs1 := sub_nonneg.mpr hs.2
  unfold plannerTransitionContribution
  positivity

/-- Collecting equal output triples in the direct sampler gives the kernel density. -/
lemma plannerJointDensity_sum {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (f : Fin n × ℝ × Finset (Fin n) → ℝ≥0∞) :
    (∑ D ∈ A.powerset.erase ∅, ∑ i ∈ D, ∑ T ∈ (A \ D).powerset,
      ENNReal.ofReal (plannerJointDensity A p D i T s) * f (i, s, D.erase i ∪ T)) =
      ∑ i ∈ A, ∑ B ∈ (A.erase i).powerset,
        ENNReal.ofReal (plannerKernelDensity A p i B s) * f (i, s, B) := by
  calc
    (∑ D ∈ A.powerset.erase ∅, ∑ i ∈ D, ∑ T ∈ (A \ D).powerset,
      ENNReal.ofReal (plannerJointDensity A p D i T s) * f (i, s, D.erase i ∪ T)) =
      ∑ z : PlannerSamplerIndex A,
        ENNReal.ofReal (plannerJointDensity A p z.1.1 z.1.2.1 z.1.2.2 s) *
          f (z.1.2.1, s, z.1.1.erase z.1.2.1 ∪ z.1.2.2) :=
        (sum_plannerSamplerIndex A _).symm
    _ = ∑ z : PlannerDensityIndex A,
        ENNReal.ofReal (plannerTransitionContribution A p z.1.1 z.1.2.1 z.1.2.2 s) *
          f (z.1.1, s, z.1.2.1) := by
      apply Fintype.sum_equiv (plannerSamplerIndexEquiv A)
      intro z
      rw [plannerJointDensity_reindex]
      rfl
    _ = ∑ i ∈ A, ∑ B ∈ (A.erase i).powerset, ∑ C ∈ B.powerset,
        ENNReal.ofReal (plannerTransitionContribution A p i B C s) * f (i, s, B) :=
      sum_plannerDensityIndex A (fun i B C =>
        ENNReal.ofReal (plannerTransitionContribution A p i B C s) * f (i, s, B))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro B hB
      have hSub : B ⊆ A.erase i := Finset.mem_powerset.mp hB
      have hPos : ∀ C ∈ B.powerset, 0 ≤ plannerTransitionContribution A p i B C s := by
        intro C hC
        exact plannerTransitionContribution_nonneg A p hp hi B
          (fun j hj => (Finset.mem_erase.mp (hSub ((Finset.mem_powerset.mp hC) hj))).2) hs
      rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg hPos,
        plannerTransitionContribution_sum A p i B s hSub]

lemma plannerJointDensity_ofReal {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) {D : Finset (Fin n)} (hD : D ⊆ A)
    (i : Fin n) (T : Finset (Fin n)) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    ENNReal.ofReal (plannerJointDensity A p D i T s) =
      ENNReal.ofReal ((∏ j ∈ D, (4 * p j)) / (plannerWeight A p - 1)) *
        (ENNReal.ofReal (1 / (D.card : ℝ)) *
          ENNReal.ofReal ((D.card : ℝ) * s ^ (D.card - 1))) *
          ENNReal.ofReal (s ^ T.card * (1 - s) ^ ((A \ D).card - T.card)) := by
  have hw := plannerNonemptySubset_weight_nonneg A p hp hD
  have hu : 0 ≤ 1 / (D.card : ℝ) := by positivity
  have hd : 0 ≤ (D.card : ℝ) * s ^ (D.card - 1) :=
    mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hs.1 _)
  unfold plannerJointDensity
  rw [mul_assoc
    (((∏ j ∈ D, (4 * p j)) / (plannerWeight A p - 1)) *
      ((1 / (D.card : ℝ)) * ((D.card : ℝ) * s ^ (D.card - 1))))
    (s ^ T.card) ((1 - s) ^ ((A \ D).card - T.card)),
    ENNReal.ofReal_mul (mul_nonneg hw (mul_nonneg hu hd)),
    ENNReal.ofReal_mul hw, ENNReal.ofReal_mul hu]

lemma lintegral_plannerTransitionLaw_eq_joint {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i)
    (f : Fin n × ℝ × Finset (Fin n) → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, f x ∂plannerTransitionLaw A p hA hp) =
      ∑ D ∈ A.powerset.erase ∅, ∑ i ∈ D, ∑ T ∈ (A \ D).powerset,
        ∫⁻ s, ENNReal.ofReal (plannerJointDensity A p D i T s) *
          f (i, s, D.erase i ∪ T) ∂Instance.uniformClock := by
  rw [lintegral_plannerTransitionLaw A p hA hp f hf]
  apply Finset.sum_congr rfl
  intro D hD
  have hDne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hD).1
  have hDA : D ⊆ A := Finset.mem_powerset.mp (Finset.mem_erase.mp hD).2
  rw [lintegral_plannerIdentityTransitionLaw A D hDne f hf, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [lintegral_plannerConditionalTransitionLaw A D hDne i f hf]
  have hM (T : Finset (Fin n)) : Measurable (fun s : ℝ =>
      ENNReal.ofReal (plannerJointDensity A p D i T s) * f (i, s, D.erase i ∪ T)) :=
    (show Measurable (fun s : ℝ => ENNReal.ofReal (plannerJointDensity A p D i T s)) from
      by unfold plannerJointDensity; fun_prop).mul
      (hf.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    ← lintegral_finsetSum (A \ D).powerset (fun T _ => hM T)]
  apply lintegral_congr_ae
  filter_upwards [uniformClock_mem_open_unit] with s hs
  have hs' : s ∈ Icc (0 : ℝ) 1 := ⟨hs.1.le, hs.2.le⟩
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro T _
  rw [plannerJointDensity_ofReal A p (fun j hj => (hp j hj).le) hDA i T hs']
  ring

/-- `lem:planner-sampler`: the complete concrete seed execution has exactly
its prescribed three-coordinate kernel law. -/
theorem plannerTransitionLaw_eq_kernelLaw {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    plannerTransitionLaw A p hA hp = plannerKernelLaw A p := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_plannerTransitionLaw_eq_joint A p hA hp f hf, lintegral_plannerKernelLaw A p f hf]
  have hMJ (D : Finset (Fin n)) (i : Fin n) (T : Finset (Fin n)) : Measurable (fun s : ℝ =>
      ENNReal.ofReal (plannerJointDensity A p D i T s) * f (i, s, D.erase i ∪ T)) :=
    (show Measurable (fun s : ℝ => ENNReal.ofReal (plannerJointDensity A p D i T s)) from
      by unfold plannerJointDensity; fun_prop).mul
      (hf.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hMK (i : Fin n) (B : Finset (Fin n)) : Measurable (fun s : ℝ =>
      ENNReal.ofReal (plannerKernelDensity A p i B s) * f (i, s, B)) :=
    (show Measurable (fun s : ℝ => ENNReal.ofReal (plannerKernelDensity A p i B s)) from
      by unfold plannerKernelDensity; fun_prop).mul
      (hf.comp (measurable_const.prodMk (measurable_id.prodMk measurable_const)))
  have hJ : (∑ D ∈ A.powerset.erase ∅, ∑ i ∈ D, ∑ T ∈ (A \ D).powerset,
      ∫⁻ s, ENNReal.ofReal (plannerJointDensity A p D i T s) *
        f (i, s, D.erase i ∪ T) ∂Instance.uniformClock) =
      ∫⁻ s, ∑ D ∈ A.powerset.erase ∅, ∑ i ∈ D, ∑ T ∈ (A \ D).powerset,
        ENNReal.ofReal (plannerJointDensity A p D i T s) *
          f (i, s, D.erase i ∪ T) ∂Instance.uniformClock := by
    symm
    rw [lintegral_finsetSum _ (fun D _ => Finset.measurable_sum _
      (fun i _ => Finset.measurable_sum _ (fun T _ => hMJ D i T)))]
    apply Finset.sum_congr rfl
    intro D _
    rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun T _ => hMJ D i T))]
    apply Finset.sum_congr rfl
    intro i _
    exact lintegral_finsetSum _ (fun T _ => hMJ D i T)
  have hK : (∑ i ∈ A, ∑ B ∈ (A.erase i).powerset,
      ∫⁻ s, ENNReal.ofReal (plannerKernelDensity A p i B s) * f (i, s, B)
        ∂Instance.uniformClock) =
      ∫⁻ s, ∑ i ∈ A, ∑ B ∈ (A.erase i).powerset,
        ENNReal.ofReal (plannerKernelDensity A p i B s) * f (i, s, B)
          ∂Instance.uniformClock := by
    symm
    rw [lintegral_finsetSum _ (fun i _ => Finset.measurable_sum _ (fun B _ => hMK i B))]
    apply Finset.sum_congr rfl
    intro i _
    exact lintegral_finsetSum _ (fun B _ => hMK i B)
  rw [hJ, hK]
  apply lintegral_congr_ae
  filter_upwards [uniformClock_mem_open_unit] with s hs
  exact plannerJointDensity_sum A p (fun i hi => (hp i hi).le) ⟨hs.1.le, hs.2.le⟩ f

end ProphetSecretary.Statistics
