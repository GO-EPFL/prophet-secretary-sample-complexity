import ProphetSecretary.Statistics.PlannerSampler
import ProphetSecretary.Probability.BernoulliSubset
import ProphetSecretary.Probability.CategoricalUniform
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Distributions.Uniform

/-!
# First-success implementation of the nonempty subset sampler

A categorical first success is followed by independent Bernoulli draws on
later identities. The first-success weights telescope, so the construction
uses no rejection sampling.
-/

open MeasureTheory Set Filter
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def plannerFirstSuccessWeight {n : ℕ} (A : Finset (Fin n))
    (p : Fin n → ℝ) (i : Fin n) : ℝ :=
  (plannerBernoulliProbability (p i) *
    ∏ j ∈ A.filter (fun j => j < i), (1 - plannerBernoulliProbability (p j))) /
    (1 - ∏ j ∈ A, (1 - plannerBernoulliProbability (p j)))

lemma plannerFirstSuccess_numerator_sum {n : ℕ} (A : Finset (Fin n)) (r : Fin n → ℝ) :
    (∑ i ∈ A, r i * ∏ j ∈ A.filter (fun j => j < i), (1 - r j)) =
      1 - ∏ i ∈ A, (1 - r i) := by
  have h := Finset.prod_add_ordered (ι := OrderDual (Fin n)) A
    (fun j => 1 - r j) r
  simp only [sub_add_cancel, Finset.prod_const_one, mul_one] at h
  change (1 : ℝ) = (∏ i ∈ A, (1 - r i)) +
    ∑ i ∈ A, r i * ∏ j ∈ A.filter (fun j => j < i), (1 - r j) at h
  linarith

lemma planner_nonempty_probability_pos {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    0 < 1 - ∏ i ∈ A, (1 - plannerBernoulliProbability (p i)) := by
  have hβ := one_lt_plannerWeight A p hA hp
  rw [plannerBernoulliFailure_prod A p (fun i hi => (hp i hi).le)]
  exact sub_pos.mpr ((div_lt_iff₀ (by linarith : 0 < plannerWeight A p)).mpr (by simpa using hβ))

lemma plannerFirstSuccessWeight_nonneg {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) {i : Fin n} (hi : i ∈ A) :
    0 ≤ plannerFirstSuccessWeight A p i := by
  unfold plannerFirstSuccessWeight
  apply div_nonneg _ (planner_nonempty_probability_pos A p hA hp).le
  apply mul_nonneg (plannerBernoulliProbability_mem_unitInterval (hp i hi).le).1
  apply Finset.prod_nonneg
  intro j hj
  exact sub_nonneg.mpr (plannerBernoulliProbability_mem_unitInterval
    (hp j (Finset.mem_filter.mp hj).1).le).2

lemma plannerFirstSuccessWeight_sum {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    (∑ i ∈ A, plannerFirstSuccessWeight A p i) = 1 := by
  simp only [plannerFirstSuccessWeight]
  rw [← Finset.sum_div, plannerFirstSuccess_numerator_sum]
  exact div_self (ne_of_gt (planner_nonempty_probability_pos A p hA hp))

noncomputable def plannerFirstSuccessPMF {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) : PMF (Fin n) := by
  let w : Fin n → ℝ≥0∞ := fun i => if i ∈ A then
    ENNReal.ofReal (plannerFirstSuccessWeight A p i) else 0
  refine PMF.ofFinset w A ?_ ?_
  · simp only [w, Finset.sum_ite_mem, Finset.inter_self]
    rw [← ENNReal.ofReal_sum_of_nonneg (fun i hi => plannerFirstSuccessWeight_nonneg A p hA hp hi),
      plannerFirstSuccessWeight_sum A p hA hp, ENNReal.ofReal_one]
  · intro i hi
    simp only [w, if_neg hi]

lemma plannerFirstSuccessPMF_apply {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) (i : Fin n) :
    plannerFirstSuccessPMF A p hA hp i =
      if i ∈ A then ENNReal.ofReal (plannerFirstSuccessWeight A p i) else 0 := rfl

noncomputable def plannerFirstSuccessSet {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (i : Fin n) (u : Fin n → ℝ) : Finset (Fin n) :=
  insert i (bernoulliSubset (A.filter (fun j => i < j)) (fun j => plannerBernoulliProbability (p j)) u)

lemma measurable_plannerFirstSuccessSet {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (i : Fin n) : Measurable (plannerFirstSuccessSet A p i) := by
  rw [measurable_finset_iff]
  intro j
  have h := measurable_finset_iff.mp (measurable_bernoulliSubset
    (A.filter (fun j => i < j)) (fun _ j => plannerBernoulliProbability (p j)) id
      (fun _ => measurable_const) (fun j => measurable_pi_apply j)) j
  simpa only [plannerFirstSuccessSet, Finset.mem_insert, id_eq] using measurable_const.or h

noncomputable def plannerFirstSuccessSubsetLaw {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) : Measure (Finset (Fin n)) :=
  (plannerFirstSuccessPMF A p hA hp).toMeasure.bind
    (fun i => (Instance.clocksLaw n).map (plannerFirstSuccessSet A p i))

instance plannerFirstSuccessSubsetLaw_probability {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    IsProbabilityMeasure (plannerFirstSuccessSubsetLaw A p hA hp) := by
  exact isProbabilityMeasure_bind (measurable_of_countable _).aemeasurable
    (Eventually.of_forall (fun i =>
      Measure.isProbabilityMeasure_map (measurable_plannerFirstSuccessSet A p i).aemeasurable))

lemma plannerFirstSuccessSet_subset {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    {i : Fin n} (hi : i ∈ A) (u : Fin n → ℝ) : plannerFirstSuccessSet A p i u ⊆ A := by
  intro j hj
  rcases Finset.mem_insert.mp hj with rfl | hj
  · exact hi
  · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).1

lemma plannerFirstSuccessSet_eq_implies_min {n : ℕ} (A D : Finset (Fin n)) (p : Fin n → ℝ)
    (hD : D.Nonempty) (i : Fin n) (u : Fin n → ℝ)
    (h : plannerFirstSuccessSet A p i u = D) : D.min' hD = i := by
  apply (Finset.min'_eq_iff D hD i).mpr
  constructor
  · rw [← h]
    exact Finset.mem_insert_self _ _
  · intro j hj
    rw [← h] at hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact le_rfl
    · exact (Finset.mem_filter.mp (Finset.mem_filter.mp hj).1).2.le

lemma plannerFirstSuccessSet_min_fiber {n : ℕ} (A D : Finset (Fin n)) (p : Fin n → ℝ)
    (hD : D.Nonempty) :
    {u | plannerFirstSuccessSet A p (D.min' hD) u = D} =
      {u | bernoulliSubset (A.filter (fun j => D.min' hD < j))
        (fun j => plannerBernoulliProbability (p j)) u = D.erase (D.min' hD)} := by
  ext u
  simp only [Set.mem_setOf_eq]
  have hk : D.min' hD ∉ bernoulliSubset (A.filter (fun j => D.min' hD < j))
      (fun j => plannerBernoulliProbability (p j)) u := by
    simp [bernoulliSubset]
  constructor
  · intro h
    have he := congrArg (fun C : Finset (Fin n) => C.erase (D.min' hD)) h
    simpa only [plannerFirstSuccessSet, Finset.erase_insert hk] using he
  · intro h
    change insert (D.min' hD) _ = D
    rw [h, Finset.insert_erase (Finset.min'_mem D hD)]

lemma plannerFirstSuccessSet_min_probability {n : ℕ} (A D : Finset (Fin n)) (p : Fin n → ℝ)
    (hp : ∀ i ∈ A, 0 ≤ p i) (hDA : D ⊆ A) (hD : D.Nonempty) :
    (Instance.clocksLaw n).real {u | plannerFirstSuccessSet A p (D.min' hD) u = D} =
      (∏ j ∈ D.erase (D.min' hD), plannerBernoulliProbability (p j)) *
        ∏ j ∈ A.filter (fun j => D.min' hD < j) \ D.erase (D.min' hD),
          (1 - plannerBernoulliProbability (p j)) := by
  rw [plannerFirstSuccessSet_min_fiber A D p hD]
  apply bernoulliSubset_probability
  · intro j hj
    exact plannerBernoulliProbability_mem_unitInterval (hp j (Finset.mem_filter.mp hj).1)
  · intro j hj
    have h := Finset.mem_erase.mp hj
    exact Finset.mem_filter.mpr ⟨hDA h.2,
      lt_of_le_of_ne (Finset.min'_le _ _ h.2) h.1.symm⟩

lemma plannerFirstSuccess_failure_partition {n : ℕ} (A D : Finset (Fin n))
    (hD : D.Nonempty) :
    (A.filter (fun j => j < D.min' hD)) ∪
      ((A.filter (fun j => D.min' hD < j)) \ D.erase (D.min' hD)) = A \ D := by
  ext j
  simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_sdiff, Finset.mem_erase]
  constructor
  · rintro (h | h)
    · refine ⟨h.1, ?_⟩
      intro hjD
      exact (not_lt_of_ge (Finset.min'_le _ _ hjD)) h.2
    · refine ⟨h.1.1, ?_⟩
      intro hjD
      exact h.2 ⟨ne_of_gt h.1.2, hjD⟩
  · intro h
    have hne : j ≠ D.min' hD := fun he => h.2 (he ▸ Finset.min'_mem D hD)
    rcases lt_or_gt_of_ne hne with hj | hj
    · exact Or.inl ⟨h.1, hj⟩
    · exact Or.inr ⟨⟨h.1, hj⟩, fun hmem => h.2 hmem.2⟩

lemma plannerFirstSuccess_min_weighted_probability {n : ℕ} (A D : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) (hDA : D ⊆ A) (hD : D.Nonempty) :
    plannerFirstSuccessWeight A p (D.min' hD) *
      (Instance.clocksLaw n).real {u | plannerFirstSuccessSet A p (D.min' hD) u = D} =
      (∏ j ∈ D, (4 * p j)) / (plannerWeight A p - 1) := by
  let r : Fin n → ℝ := fun j => plannerBernoulliProbability (p j)
  have hDis : Disjoint (A.filter (fun j => j < D.min' hD))
      ((A.filter (fun j => D.min' hD < j)) \ D.erase (D.min' hD)) := by
    apply Finset.disjoint_left.mpr
    intro j hj1 hj2
    exact (not_lt_of_ge (Finset.mem_filter.mp hj1).2.le)
      (Finset.mem_filter.mp (Finset.mem_sdiff.mp hj2).1).2
  have hFailure : (∏ j ∈ A.filter (fun j => j < D.min' hD), (1 - r j)) *
      (∏ j ∈ A.filter (fun j => D.min' hD < j) \ D.erase (D.min' hD), (1 - r j)) =
        ∏ j ∈ A \ D, (1 - r j) := by
    rw [← Finset.prod_union hDis, plannerFirstSuccess_failure_partition A D hD]
  have hSuccess := Finset.mul_prod_erase D r (Finset.min'_mem D hD)
  rw [plannerFirstSuccessSet_min_probability A D p (fun i hi => (hp i hi).le) hDA hD]
  calc
    plannerFirstSuccessWeight A p (D.min' hD) *
        ((∏ j ∈ D.erase (D.min' hD), r j) *
          ∏ j ∈ A.filter (fun j => D.min' hD < j) \ D.erase (D.min' hD), (1 - r j)) =
      ((r (D.min' hD) * ∏ j ∈ D.erase (D.min' hD), r j) *
        ((∏ j ∈ A.filter (fun j => j < D.min' hD), (1 - r j)) *
          ∏ j ∈ A.filter (fun j => D.min' hD < j) \ D.erase (D.min' hD), (1 - r j))) /
            (1 - ∏ j ∈ A, (1 - r j)) := by
      unfold plannerFirstSuccessWeight
      dsimp [r]
      ring
    _ = ((∏ j ∈ D, r j) * ∏ j ∈ A \ D, (1 - r j)) /
        (1 - ∏ j ∈ A, (1 - r j)) := by rw [hSuccess, hFailure]
    _ = _ := plannerBernoulliSubset_conditional_mass A p hA hp hDA

lemma plannerFirstSuccessSubsetLaw_singleton {n : ℕ} (A D : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    plannerFirstSuccessSubsetLaw A p hA hp {D} =
      ∑ i ∈ A, ENNReal.ofReal (plannerFirstSuccessWeight A p i) *
        (Instance.clocksLaw n) {u | plannerFirstSuccessSet A p i u = D} := by
  rw [plannerFirstSuccessSubsetLaw,
    Measure.bind_apply (measurableSet_singleton D) (measurable_of_countable _).aemeasurable,
    lintegral_fintype]
  simp only [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
    plannerFirstSuccessPMF_apply, mul_ite, mul_zero, Finset.sum_ite_mem, Finset.univ_inter]
  apply Finset.sum_congr rfl
  intro i _
  rw [Measure.map_apply (measurable_plannerFirstSuccessSet A p i) (measurableSet_singleton D)]
  change (Instance.clocksLaw n) {u | plannerFirstSuccessSet A p i u = D} *
    ENNReal.ofReal (plannerFirstSuccessWeight A p i) = _
  exact mul_comm _ _

/-- The first-success algorithm has the required nonempty-subset law. -/
theorem plannerFirstSuccessSubsetLaw_eq_nonemptySubsetPMF {n : ℕ} (A : Finset (Fin n))
    (p : Fin n → ℝ) (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    plannerFirstSuccessSubsetLaw A p hA hp = (plannerNonemptySubsetPMF A p hA hp).toMeasure := by
  apply Measure.ext_of_singleton
  intro D
  rw [plannerFirstSuccessSubsetLaw_singleton A D p hA hp,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton D), plannerNonemptySubsetPMF_apply]
  by_cases hD : D ∈ A.powerset.erase ∅
  · have hDne : D.Nonempty := Finset.nonempty_iff_ne_empty.mpr (Finset.mem_erase.mp hD).1
    have hDA : D ⊆ A := Finset.mem_powerset.mp (Finset.mem_erase.mp hD).2
    have hk : D.min' hDne ∈ A := hDA (Finset.min'_mem D hDne)
    rw [if_pos hD, Finset.sum_eq_single_of_mem (D.min' hDne) hk]
    · have hMass : (Instance.clocksLaw n) {u | plannerFirstSuccessSet A p (D.min' hDne) u = D} =
        ENNReal.ofReal ((Instance.clocksLaw n).real
          {u | plannerFirstSuccessSet A p (D.min' hDne) u = D}) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      rw [hMass, ← ENNReal.ofReal_mul (plannerFirstSuccessWeight_nonneg A p hA hp hk),
        plannerFirstSuccess_min_weighted_probability A D p hA hp hDA hDne]
    · intro i _ hne
      have he : {u | plannerFirstSuccessSet A p i u = D} = ∅ := by
        ext u
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        intro h
        exact hne (plannerFirstSuccessSet_eq_implies_min A D p hDne i u h).symm
      rw [he, measure_empty, mul_zero]
  · rw [if_neg hD]
    apply Finset.sum_eq_zero
    intro i hi
    have he : {u | plannerFirstSuccessSet A p i u = D} = ∅ := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      have hDA : D ⊆ A := by
        rw [← h]
        exact plannerFirstSuccessSet_subset A p hi u
      have hDne : D.Nonempty := by
        rw [← h]
        exact ⟨i, Finset.mem_insert_self _ _⟩
      exact hD (Finset.mem_erase.mpr ⟨hDne.ne_empty, Finset.mem_powerset.mpr hDA⟩)
    rw [he, measure_empty, mul_zero]

noncomputable def plannerFirstSuccessChoice {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (u : ℝ) : Fin n :=
  categoricalUniformSample A hA (plannerFirstSuccessWeight A p) u

lemma measurable_plannerFirstSuccessChoice {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) : Measurable (plannerFirstSuccessChoice A p hA) :=
  measurable_categoricalUniformSample A hA _

lemma map_plannerFirstSuccessChoice {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    Instance.uniformClock.map (plannerFirstSuccessChoice A p hA) =
      (plannerFirstSuccessPMF A p hA hp).toMeasure := by
  exact map_categoricalUniformSample_eq_pmf A hA (plannerFirstSuccessWeight A p)
    (fun i hi => plannerFirstSuccessWeight_nonneg A p hA hp hi)
    (plannerFirstSuccessWeight_sum A p hA hp) _ (plannerFirstSuccessPMF_apply A p hA hp)

/-- Nonempty subset sampled from the same uniform seed space for every
active set and every vector of positive probabilities. -/
noncomputable def plannerFirstSuccessUniform {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (seed : ℝ × (Fin n → ℝ)) : Finset (Fin n) :=
  plannerFirstSuccessSet A p (plannerFirstSuccessChoice A p hA seed.1) seed.2

lemma measurable_plannerFirstSuccessUniform {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) : Measurable (plannerFirstSuccessUniform A p hA) := by
  have hJoint : Measurable (fun z : Fin n × (Fin n → ℝ) => plannerFirstSuccessSet A p z.1 z.2) :=
    measurable_from_prod_countable_right (fun i => measurable_plannerFirstSuccessSet A p i)
  exact hJoint.comp (((measurable_plannerFirstSuccessChoice A p hA).comp measurable_fst).prodMk
    measurable_snd)

lemma plannerFirstSuccessUniform_nonempty {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (seed : ℝ × (Fin n → ℝ)) :
    (plannerFirstSuccessUniform A p hA seed).Nonempty :=
  ⟨_, Finset.mem_insert_self _ _⟩

lemma plannerFirstSuccessUniform_subset {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (seed : ℝ × (Fin n → ℝ)) : plannerFirstSuccessUniform A p hA seed ⊆ A :=
  plannerFirstSuccessSet_subset A p (categoricalUniformSample_mem A hA _ _) _

lemma map_plannerFirstSuccessUniform_eq_subsetLaw {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    (Instance.uniformClock.prod (Instance.clocksLaw n)).map (plannerFirstSuccessUniform A p hA) =
      plannerFirstSuccessSubsetLaw A p hA hp := by
  apply Measure.ext_of_lintegral
  intro f hf
  rw [lintegral_map hf (measurable_plannerFirstSuccessUniform A p hA)]
  change (∫⁻ seed, (f ∘ plannerFirstSuccessUniform A p hA) seed
    ∂Instance.uniformClock.prod (Instance.clocksLaw n)) = _
  rw [lintegral_prod _ (hf.comp (measurable_plannerFirstSuccessUniform A p hA)).aemeasurable,
    plannerFirstSuccessSubsetLaw,
    Measure.lintegral_bind (measurable_of_countable _).aemeasurable hf.aemeasurable]
  have hEach (i : Fin n) :
      (∫⁻ D, f D ∂(Instance.clocksLaw n).map (plannerFirstSuccessSet A p i)) =
        ∫⁻ u, f (plannerFirstSuccessSet A p i u) ∂Instance.clocksLaw n :=
    lintegral_map hf (measurable_plannerFirstSuccessSet A p i)
  simp_rw [hEach]
  rw [← map_plannerFirstSuccessChoice A p hA hp]
  exact (lintegral_map (measurable_of_countable
    (fun i => ∫⁻ u, f (plannerFirstSuccessSet A p i u) ∂Instance.clocksLaw n))
      (measurable_plannerFirstSuccessChoice A p hA)).symm

/-- The efficient first-success map produces the prescribed nonempty-subset
PMF from a state-independent product of uniform seeds. -/
theorem map_plannerFirstSuccessUniform {n : ℕ} (A : Finset (Fin n)) (p : Fin n → ℝ)
    (hA : A.Nonempty) (hp : ∀ i ∈ A, 0 < p i) :
    (Instance.uniformClock.prod (Instance.clocksLaw n)).map (plannerFirstSuccessUniform A p hA) =
      (plannerNonemptySubsetPMF A p hA hp).toMeasure := by
  rw [map_plannerFirstSuccessUniform_eq_subsetLaw A p hA hp,
    plannerFirstSuccessSubsetLaw_eq_nonemptySubsetPMF A p hA hp]

end ProphetSecretary.Statistics
