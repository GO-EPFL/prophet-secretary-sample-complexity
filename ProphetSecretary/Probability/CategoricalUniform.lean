import ProphetSecretary.Probability.OrderCDFUniform
import Mathlib.Probability.Distributions.Uniform

/-!
# Sampling a finite categorical law from one uniform

Cumulative masses are tested in increasing identity order. The implementation
is total on every real seed; the maximal identity is its fallback.
-/

open MeasureTheory Set
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Probability

noncomputable def categoricalPrefix {n : ℕ} (A : Finset (Fin n)) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ A.filter (fun j => j ≤ i), w j

noncomputable def categoricalBefore {n : ℕ} (A : Finset (Fin n)) (w : Fin n → ℝ) (i : Fin n) : ℝ :=
  ∑ j ∈ A.filter (fun j => j < i), w j

noncomputable def categoricalUniformSample {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (w : Fin n → ℝ) (u : ℝ) : Fin n :=
  A.inf' hA (fun i => if u < categoricalPrefix A w i then i else A.max' hA)

lemma categoricalPrefix_at_max {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty) (w : Fin n → ℝ) :
    categoricalPrefix A w (A.max' hA) = ∑ i ∈ A, w i := by
  unfold categoricalPrefix
  rw [Finset.filter_true_of_mem (fun j hj => Finset.le_max' A j hj)]

lemma categoricalPrefix_eq_before_add {n : ℕ} (A : Finset (Fin n)) (w : Fin n → ℝ)
    {i : Fin n} (hi : i ∈ A) : categoricalPrefix A w i = categoricalBefore A w i + w i := by
  have hSet : A.filter (fun j => j ≤ i) = insert i (A.filter (fun j => j < i)) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hj, hji⟩
      rcases eq_or_lt_of_le hji with rfl | hlt
      · exact Or.inl rfl
      · exact Or.inr ⟨hj, hlt⟩
    · rintro (rfl | h)
      · exact ⟨hi, le_rfl⟩
      · exact ⟨h.1, h.2.le⟩
  unfold categoricalPrefix categoricalBefore
  rw [hSet, Finset.sum_insert (by simp), add_comm]

lemma categoricalPrefix_le_before {n : ℕ} (A : Finset (Fin n)) (w : Fin n → ℝ)
    (hw : ∀ i ∈ A, 0 ≤ w i) {j i : Fin n} (hji : j < i) :
    categoricalPrefix A w j ≤ categoricalBefore A w i := by
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro k hk
    have h := Finset.mem_filter.mp hk
    exact Finset.mem_filter.mpr ⟨h.1, h.2.trans_lt hji⟩
  · intro k hk _
    exact hw k (Finset.mem_filter.mp hk).1

lemma categoricalBefore_le_of_no_crossing {n : ℕ} (A : Finset (Fin n)) (w : Fin n → ℝ)
    (i : Fin n) {u : ℝ} (hu : 0 ≤ u)
    (h : ∀ j ∈ A, j < i → categoricalPrefix A w j ≤ u) : categoricalBefore A w i ≤ u := by
  let B := A.filter (fun j => j < i)
  by_cases hB : B.Nonempty
  · have hBmem : B.max' hB ∈ A ∧ B.max' hB < i := Finset.mem_filter.mp (Finset.max'_mem B hB)
    have hSet : A.filter (fun j => j ≤ B.max' hB) = B := by
      ext j
      constructor
      · intro hj
        have hj' := Finset.mem_filter.mp hj
        exact Finset.mem_filter.mpr ⟨hj'.1, hj'.2.trans_lt hBmem.2⟩
      · intro hj
        exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hj).1, Finset.le_max' B j hj⟩
    have he : categoricalPrefix A w (B.max' hB) = categoricalBefore A w i := by
      unfold categoricalPrefix categoricalBefore
      rw [hSet]
    rw [← he]
    exact h _ hBmem.1 hBmem.2
  · have he : B = ∅ := Finset.not_nonempty_iff_eq_empty.mp hB
    change (∑ j ∈ B, w j) ≤ u
    simpa only [he, Finset.sum_empty] using hu

lemma categoricalUniformSample_mem {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (w : Fin n → ℝ) (u : ℝ) : categoricalUniformSample A hA w u ∈ A := by
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' hA
    (fun j => if u < categoricalPrefix A w j then j else A.max' hA)
  unfold categoricalUniformSample
  rw [he]
  split_ifs
  · exact hj
  · exact Finset.max'_mem A hA

lemma categoricalUniformSample_first {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (w : Fin n → ℝ) (hSum : ∑ i ∈ A, w i = 1) {u : ℝ} (hu : u < 1) :
    u < categoricalPrefix A w (categoricalUniformSample A hA w u) ∧
      ∀ j ∈ A, u < categoricalPrefix A w j → categoricalUniformSample A hA w u ≤ j := by
  let C := A.filter (fun j => u < categoricalPrefix A w j)
  have hMax : A.max' hA ∈ C := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.max'_mem A hA, by rwa [categoricalPrefix_at_max, hSum]⟩
  have hC : C.Nonempty := ⟨_, hMax⟩
  have hcA : C.min' hC ∈ A := (Finset.mem_filter.mp (Finset.min'_mem C hC)).1
  have hcU : u < categoricalPrefix A w (C.min' hC) :=
    (Finset.mem_filter.mp (Finset.min'_mem C hC)).2
  have he : categoricalUniformSample A hA w u = C.min' hC := by
    unfold categoricalUniformSample
    apply le_antisymm
    · have h := Finset.inf'_le (fun i => if u < categoricalPrefix A w i then i else A.max' hA) hcA
      simpa only [if_pos hcU] using h
    · apply Finset.le_inf' hA
      intro j hj
      by_cases hju : u < categoricalPrefix A w j
      · rw [if_pos hju]
        exact Finset.min'_le C j (Finset.mem_filter.mpr ⟨hj, hju⟩)
      · rw [if_neg hju]
        exact Finset.le_max' A _ hcA
  rw [he]
  refine ⟨hcU, ?_⟩
  intro j hj hju
  exact Finset.min'_le C j (Finset.mem_filter.mpr ⟨hj, hju⟩)

lemma categoricalUniformSample_fiber_unit {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (w : Fin n → ℝ) (hw : ∀ i ∈ A, 0 ≤ w i) (hSum : ∑ i ∈ A, w i = 1)
    {i : Fin n} (hi : i ∈ A) {u : ℝ} (hu : u ∈ Ico (0 : ℝ) 1) :
    categoricalUniformSample A hA w u = i ↔
      u ∈ Ico (categoricalBefore A w i) (categoricalPrefix A w i) := by
  have hFirst := categoricalUniformSample_first A hA w hSum hu.2
  constructor
  · intro he
    rw [he] at hFirst
    refine ⟨categoricalBefore_le_of_no_crossing A w i hu.1 ?_, hFirst.1⟩
    intro j hj hji
    exact le_of_not_gt (fun hju => (not_le_of_gt hji) (hFirst.2 j hj hju))
  · intro huI
    apply le_antisymm (hFirst.2 i hi huI.2)
    by_contra hNot
    have hlt : categoricalUniformSample A hA w u < i := lt_of_not_ge hNot
    have hBound := categoricalPrefix_le_before A w hw hlt
    exact (not_lt_of_ge (hBound.trans huI.1)) hFirst.1

lemma measurable_categoricalUniformSample {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (w : Fin n → ℝ) : Measurable (categoricalUniformSample A hA w) := by
  have h : Measurable (A.inf' hA (fun i (u : ℝ) =>
      if u < categoricalPrefix A w i then i else A.max' hA)) :=
    Finset.inf'_induction hA _ (fun _f hf _g hg => hf.inf hg)
      (fun i _ => measurable_const.ite (measurableSet_lt measurable_id measurable_const) measurable_const)
  convert h using 1
  funext u
  simp only [categoricalUniformSample, Finset.inf'_apply]

lemma uniformClock_Ico_of_bounds {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 1) :
    Model.Instance.uniformClock (Ico a b) = ENNReal.ofReal (b - a) := by
  have hSub : Ico a b ⊆ Icc (0 : ℝ) 1 := by
    intro u hu
    exact ⟨ha.trans hu.1, hu.2.le.trans hb⟩
  rw [Model.Instance.uniformClock, Measure.restrict_apply measurableSet_Ico,
    Set.inter_eq_left.mpr hSub, Real.volume_Ico]

lemma map_categoricalUniformSample_apply {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (w : Fin n → ℝ) (hw : ∀ i ∈ A, 0 ≤ w i) (hSum : ∑ i ∈ A, w i = 1) (i : Fin n) :
    (Model.Instance.uniformClock.map (categoricalUniformSample A hA w)) {i} =
      if i ∈ A then ENNReal.ofReal (w i) else 0 := by
  rw [Measure.map_apply (measurable_categoricalUniformSample A hA w) (measurableSet_singleton i)]
  by_cases hi : i ∈ A
  · rw [if_pos hi]
    have hEq : (categoricalUniformSample A hA w) ⁻¹' {i} =ᵐ[Model.Instance.uniformClock]
        Ico (categoricalBefore A w i) (categoricalPrefix A w i) := by
      filter_upwards [uniformClock_mem_open_unit] with u hu
      exact propext (categoricalUniformSample_fiber_unit A hA w hw hSum hi ⟨hu.1.le, hu.2⟩)
    rw [measure_congr hEq]
    have hBefore : 0 ≤ categoricalBefore A w i :=
      Finset.sum_nonneg (fun j hj => hw j (Finset.mem_filter.mp hj).1)
    have hPrefix : categoricalPrefix A w i ≤ 1 := by
      rw [← hSum]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun j hj _ => hw j hj)
    rw [uniformClock_Ico_of_bounds hBefore hPrefix, categoricalPrefix_eq_before_add A w hi]
    congr 1
    ring
  · rw [if_neg hi]
    have he : (categoricalUniformSample A hA w) ⁻¹' {i} = ∅ := by
      ext u
      simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
      intro h
      exact hi (h ▸ categoricalUniformSample_mem A hA w u)
    rw [he, measure_empty]

/-- The concrete cumulative sampler realizes any prescribed finite PMF with
these masses using one fixed uniform seed. -/
theorem map_categoricalUniformSample_eq_pmf {n : ℕ} (A : Finset (Fin n)) (hA : A.Nonempty)
    (w : Fin n → ℝ) (hw : ∀ i ∈ A, 0 ≤ w i) (hSum : ∑ i ∈ A, w i = 1)
    (p : PMF (Fin n)) (hp : ∀ i, p i = if i ∈ A then ENNReal.ofReal (w i) else 0) :
    Model.Instance.uniformClock.map (categoricalUniformSample A hA w) = p.toMeasure := by
  apply Measure.ext_of_singleton
  intro i
  rw [map_categoricalUniformSample_apply A hA w hw hSum,
    PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton i), hp]

end ProphetSecretary.Probability
