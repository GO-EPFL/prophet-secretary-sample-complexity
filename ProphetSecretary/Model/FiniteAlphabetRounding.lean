import ProphetSecretary.Model.FiniteAlphabetInstance
import ProphetSecretary.Probability.FiniteRoundingProduct

/-!
# Benchmark and tail counts under finite probability rounding

Moving atom mass to zero decreases every nonnegative-level tail count and
the prophet benchmark. For offers in [0,1], the benchmark decreases by at
most the sum of the moved masses. These estimates preserve the admissible
nature family in `con:bounded-learner`.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model
open ProphetSecretary.Probability

variable {n : ℕ} {Θ : Type*} [Fintype Θ] [DecidableEq Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

omit [DecidableEq Θ] in
lemma finiteAlphabetInstance_integral_maximum (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) :
    (∫ a, Instance.maximum (fun i => v (a i)) ∂Measure.pi (fun i => finiteSimplexLaw (p i) (hp i))) =
      (finiteAlphabetInstance v hv p hp).expectedMaximum :=
  (finiteAlphabetInstance_value_map v hv p hp).hasLaw.integral_comp Instance.measurable_maximum.aestronglyMeasurable

omit [DecidableEq Θ] in
lemma finiteAlphabetInstance_real_tail (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) (i : Fin n) (b : ℝ) :
    ((finiteAlphabetInstance v hv p hp).law i).real (Ioi b) =
      ∑ a, p i a*(if b<v a then (1 : ℝ) else 0) := by
  have hMP : MeasurePreserving v (finiteSimplexLaw (p i) (hp i)) ((finiteAlphabetInstance v hv p hp).law i) :=
    ⟨measurable_of_finite v,rfl⟩
  have hMean := hMP.hasLaw.integral_comp
    ((measurable_const : Measurable (fun _ : ℝ => (1 : ℝ))).indicator (measurableSet_Ioi (a:=b))).aestronglyMeasurable
  rw [integral_indicator_const _ measurableSet_Ioi,smul_eq_mul,mul_one] at hMean
  rw [← hMean,integral_finiteSimplexLaw]
  rfl

lemma finiteAlphabetInstance_rounding_tailCount_le (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N)
    (z : Θ) (hz : v z=0) {b : ℝ} (hb : 0≤b) :
    (finiteAlphabetInstance v hv (fun i => roundedProbability (p i) N z)
      (fun i => roundedProbability_simplex (p i) (hp i) hN z)).tailCount b ≤
      (finiteAlphabetInstance v hv p hp).tailCount b := by
  unfold Instance.tailCount
  change (∑ i, ((finiteAlphabetInstance v hv (fun i => roundedProbability (p i) N z)
    (fun i => roundedProbability_simplex (p i) (hp i) hN z)).law i).real (Ioi b)) ≤ _
  change (∑ i, ((finiteAlphabetInstance v hv (fun i => roundedProbability (p i) N z)
    (fun i => roundedProbability_simplex (p i) (hp i) hN z)).law i).real (Ioi b)) ≤
      ∑ i, ((finiteAlphabetInstance v hv p hp).law i).real (Ioi b)
  simp_rw [finiteAlphabetInstance_real_tail]
  apply Finset.sum_le_sum
  intro i _
  apply Finset.sum_le_sum
  intro a _
  by_cases ha : a=z
  · subst a
    simp [hz,not_lt.mpr hb]
  · apply mul_le_mul_of_nonneg_right _ (by split_ifs <;> positivity)
    rw [roundedProbability_nonzero (p i) N z a ha]
    exact floorProbability_le hN ((hp i).1 a)

lemma finiteAlphabetInstance_rounding_maximum_le (v : Θ → ℝ) (hv : ∀ a, 0≤v a)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N)
    (z : Θ) (hz : v z=0) :
    (finiteAlphabetInstance v hv (fun i => roundedProbability (p i) N z)
      (fun i => roundedProbability_simplex (p i) (hp i) hN z)).expectedMaximum ≤
      (finiteAlphabetInstance v hv p hp).expectedMaximum := by
  let γ := roundingProductCoupling p hp N hN z
  have hF := (finiteAlphabetInstance_value_map v hv p hp).comp (roundingProductCoupling_fst p hp N hN z)
  have hG := (finiteAlphabetInstance_value_map v hv _ _).comp (roundingProductCoupling_snd p hp N hN z)
  change (∫ x, Instance.maximum x ∂(finiteAlphabetInstance v hv _ _).valuesLaw) ≤
    ∫ x, Instance.maximum x ∂(finiteAlphabetInstance v hv p hp).valuesLaw
  rw [← hF.hasLaw.integral_comp Instance.measurable_maximum.aestronglyMeasurable,
    ← hG.hasLaw.integral_comp Instance.measurable_maximum.aestronglyMeasurable]
  apply integral_mono_ae (Integrable.of_finite) (Integrable.of_finite)
  filter_upwards [roundingProductCoupling_value_le p hp N hN z v hv hz] with a ha
  change Instance.maximum (fun i => v (a i).2) ≤ Instance.maximum (fun i => v (a i).1)
  exact Instance.maximum_le _ (Instance.maximum_nonnegative _) (fun i =>
    (ha i).trans (Instance.le_maximum (fun j => v (a j).1) i))

lemma finiteAlphabetInstance_rounding_maximum_error (v : Θ → ℝ) (hv : ∀ a, v a∈Icc (0 : ℝ) 1)
    (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ) (N : ℕ) (hN : 0<N) (z : Θ) :
    |(finiteAlphabetInstance v (fun a => (hv a).1) p hp).expectedMaximum-
      (finiteAlphabetInstance v (fun a => (hv a).1) (fun i => roundedProbability (p i) N z)
        (fun i => roundedProbability_simplex (p i) (hp i) hN z)).expectedMaximum| ≤
      ∑ i, roundingLoss (p i) N z := by
  let f : (Fin n → Θ) × Unit → ℝ := fun a => Instance.maximum (fun i => v (a.1 i))
  have hf : ∀ a, 0≤f a ∧ f a≤1 := fun a => ⟨Instance.maximum_nonnegative _,
    Instance.maximum_le _ (by norm_num) (fun i => (hv (a.1 i)).2)⟩
  have h := roundingProductCoupling_observable_error (Measure.dirac ()) p hp N hN z f
    (measurable_of_finite f) (by norm_num : (0 : ℝ)≤1) hf
  have hUnit (μ : Measure (Fin n → Θ)) [IsProbabilityMeasure μ] :
      (∫ a, f a ∂μ.prod (Measure.dirac ())) = ∫ a, Instance.maximum (fun i => v (a i)) ∂μ := by
    rw [integral_prod f (Integrable.of_finite)]
    simp only [f,integral_const,probReal_univ,one_smul]
  rw [hUnit,hUnit,finiteAlphabetInstance_integral_maximum v (fun a => (hv a).1) p hp,
    finiteAlphabetInstance_integral_maximum v (fun a => (hv a).1)
      (fun i => roundedProbability (p i) N z) (fun i => roundedProbability_simplex (p i) (hp i) hN z),one_mul] at h
  exact h

end ProphetSecretary.Model
