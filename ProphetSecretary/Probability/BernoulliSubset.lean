import ProphetSecretary.Probability.OrderCDFUniform

/-!
# Independent Bernoulli subsets from uniform draws

Thresholding one independent uniform per identity produces the prescribed
product law on subsets. Unused uniform coordinates have no effect.
-/

open MeasureTheory Set
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Probability

noncomputable def bernoulliSubset {n : ℕ} (A : Finset (Fin n))
    (r : Fin n → ℝ) (u : Fin n → ℝ) : Finset (Fin n) :=
  A.filter (fun i => u i ≤ r i)

lemma measurable_bernoulliSubset {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (A : Finset (Fin n)) (r u : Ω → Fin n → ℝ)
    (hr : ∀ i, Measurable (fun ω => r ω i))
    (hu : ∀ i, Measurable (fun ω => u ω i)) :
    Measurable (fun ω => bernoulliSubset A (r ω) (u ω)) := by
  rw [measurable_finset_iff]
  intro i
  simpa only [bernoulliSubset, Finset.mem_filter] using
    (measurable_const.and (measurableSet_setOf.mp (measurableSet_le (hu i) (hr i))))

lemma bernoulliSubset_fiber {n : ℕ} (A B : Finset (Fin n)) (r : Fin n → ℝ)
    (hB : B ⊆ A) :
    {u | bernoulliSubset A r u = B} = Set.univ.pi (fun i : Fin n =>
      if i ∈ A then if i ∈ B then Iic (r i) else Ioi (r i) else Set.univ) := by
  ext u
  simp only [Set.mem_setOf_eq, Set.mem_pi, Set.mem_univ, forall_true_left]
  constructor
  · intro h i
    have hi : (i ∈ A ∧ u i ≤ r i) ↔ i ∈ B := by
      simpa only [bernoulliSubset, Finset.mem_filter] using
        Iff.of_eq (congrArg (fun C : Finset (Fin n) => i ∈ C) h)
    by_cases hiA : i ∈ A
    · by_cases hiB : i ∈ B
      · simpa only [if_pos hiA, if_pos hiB, Set.mem_Iic] using (hi.mpr hiB).2
      · simp only [if_pos hiA, if_neg hiB, Set.mem_Ioi]
        exact lt_of_not_ge (fun hui => hiB (hi.mp ⟨hiA, hui⟩))
    · simp only [if_neg hiA, Set.mem_univ]
  · intro h
    ext i
    by_cases hiA : i ∈ A
    · by_cases hiB : i ∈ B
      · have hui : u i ≤ r i := by
          simpa only [if_pos hiA, if_pos hiB, Set.mem_Iic] using h i
        simp [bernoulliSubset, hiA, hiB, hui]
      · have hui : r i < u i := by
          simpa only [if_pos hiA, if_neg hiB, Set.mem_Ioi] using h i
        simp [bernoulliSubset, hiA, hiB, not_le.mpr hui]
    · have hiB : i ∉ B := fun hi => hiA (hB hi)
      simp [bernoulliSubset, hiA, hiB]

lemma measurableSet_bernoulliSubset_fiber {n : ℕ} (A B : Finset (Fin n))
    (r : Fin n → ℝ) : MeasurableSet {u | bernoulliSubset A r u = B} := by
  by_cases hB : B ⊆ A
  · rw [bernoulliSubset_fiber A B r hB]
    apply MeasurableSet.univ_pi
    intro i
    split_ifs <;> measurability
  · have he : {u | bernoulliSubset A r u = B} = ∅ := by
      ext u
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      apply hB
      rw [← h]
      exact Finset.filter_subset _ _
    rw [he]
    exact MeasurableSet.empty

lemma bernoulliSubset_probability {n : ℕ} (A B : Finset (Fin n)) (r : Fin n → ℝ)
    (hr : ∀ i ∈ A, r i ∈ Icc (0 : ℝ) 1) (hB : B ⊆ A) :
    (Model.Instance.clocksLaw n).real {u | bernoulliSubset A r u = B} =
      (∏ i ∈ B, r i) * ∏ i ∈ A \ B, (1 - r i) := by
  change ((Model.Instance.clocksLaw n) {u | bernoulliSubset A r u = B}).toReal = _
  rw [bernoulliSubset_fiber A B r hB, Model.Instance.clocksLaw, Measure.pi_pi,
    ENNReal.toReal_prod]
  have hFactor (i : Fin n) :
      (Model.Instance.uniformClock (if i ∈ A then if i ∈ B then Iic (r i)
        else Ioi (r i) else Set.univ)).toReal =
      (if i ∈ B then r i else 1) * (if i ∈ A \ B then 1 - r i else 1) := by
    by_cases hiA : i ∈ A
    · by_cases hiB : i ∈ B
      · have hsd : i ∉ A \ B := fun h => (Finset.mem_sdiff.mp h).2 hiB
        simp only [if_pos hiA, if_pos hiB, if_neg hsd, mul_one]
        change Model.Instance.uniformClock.real (Iic (r i)) = _
        rw [uniformClock_lowerCDF, min_eq_left (hr i hiA).2, max_eq_left (hr i hiA).1]
      · have hsd : i ∈ A \ B := Finset.mem_sdiff.mpr ⟨hiA, hiB⟩
        simp only [if_pos hiA, if_neg hiB, if_pos hsd, one_mul]
        rw [uniformClock_tail (hr i hiA).1, ENNReal.toReal_ofReal (sub_nonneg.mpr (hr i hiA).2)]
    · have hiB : i ∉ B := fun hi => hiA (hB hi)
      simp [hiA, hiB]
  simp_rw [hFactor]
  rw [Finset.prod_mul_distrib, Finset.prod_ite_mem_eq, Finset.prod_ite_mem_eq]

lemma bernoulliSubset_constant_probability {n : ℕ} (A B : Finset (Fin n))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (hB : B ⊆ A) :
    (Model.Instance.clocksLaw n).real {u | bernoulliSubset A (fun _ => s) u = B} =
      s ^ B.card * (1 - s) ^ (A.card - B.card) := by
  rw [bernoulliSubset_probability A B _ (fun _ _ => hs) hB]
  simp only [Finset.prod_const, Finset.card_sdiff_of_subset hB]

/-- Exact nonnegative expectation under the subset map of the actual uniform
vector. No independence premise is imposed on an abstract subset law. -/
lemma lintegral_bernoulliSubset_constant {n : ℕ} (A : Finset (Fin n))
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) (f : Finset (Fin n) → ℝ≥0∞) :
    (∫⁻ u, f (bernoulliSubset A (fun _ => s) u) ∂Model.Instance.clocksLaw n) =
      ∑ B ∈ A.powerset,
        ENNReal.ofReal (s ^ B.card * (1 - s) ^ (A.card - B.card)) * f B := by
  have hExpand (u : Fin n → ℝ) : f (bernoulliSubset A (fun _ => s) u) =
      ∑ B ∈ A.powerset, if bernoulliSubset A (fun _ => s) u = B then f B else 0 := by
    have hMem : bernoulliSubset A (fun _ => s) u ∈ A.powerset :=
      Finset.mem_powerset.mpr (Finset.filter_subset _ _)
    simp [hMem]
  simp_rw [hExpand]
  rw [lintegral_finsetSum A.powerset (fun B _ =>
    measurable_const.ite (measurableSet_bernoulliSubset_fiber A B _) measurable_const)]
  apply Finset.sum_congr rfl
  intro B hB
  have hMass : (Model.Instance.clocksLaw n) {u | bernoulliSubset A (fun _ => s) u = B} =
      ENNReal.ofReal (s ^ B.card * (1 - s) ^ (A.card - B.card)) := by
    rw [← bernoulliSubset_constant_probability A B hs (Finset.mem_powerset.mp hB)]
    exact (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  calc
    (∫⁻ u, if bernoulliSubset A (fun _ => s) u = B then f B else 0
        ∂Model.Instance.clocksLaw n) =
      ∫⁻ u in {u | bernoulliSubset A (fun _ => s) u = B}, f B
        ∂Model.Instance.clocksLaw n := by
      rw [← lintegral_indicator (measurableSet_bernoulliSubset_fiber A B _)]
      apply lintegral_congr
      intro u
      simp only [Set.indicator_apply, Set.mem_setOf_eq]
    _ = _ := by rw [lintegral_const, Measure.restrict_apply_univ, hMass, mul_comm]

end ProphetSecretary.Probability
