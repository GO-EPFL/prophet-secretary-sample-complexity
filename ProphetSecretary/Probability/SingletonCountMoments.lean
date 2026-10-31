import ProphetSecretary.Analysis.SecondMomentSupport
import Mathlib.Probability.Independence.Integration
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real

/-!
# Counts of a fixed value in independent coordinates

The mean and pair moments are computed from the actual product law. A mean
at least two therefore gives probability at least one sixth of two or more
occurrences, without any finite-support assumption on the marginal laws.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def singletonBit (a : ℝ) (x : Fin n → ℝ) (i : Fin n) : ℝ := if x i = a then 1 else 0
noncomputable def singletonCount (a : ℝ) (x : Fin n → ℝ) : ℝ := ∑ i, singletonBit a x i

lemma singletonBit_bounds (a : ℝ) (x : Fin n → ℝ) (i : Fin n) :
    0 ≤ singletonBit a x i ∧ singletonBit a x i ≤ 1 := by
  unfold singletonBit
  split_ifs <;> norm_num
lemma measurable_singletonBit (a : ℝ) (i : Fin n) : Measurable (fun x => singletonBit a x i) :=
  Measurable.ite (measurableSet_eq_fun (measurable_pi_apply i) measurable_const) measurable_const measurable_const
lemma singletonCount_bounds (a : ℝ) (x : Fin n → ℝ) :
    0 ≤ singletonCount a x ∧ singletonCount a x ≤ n := by
  constructor
  · exact Finset.sum_nonneg fun i _ => (singletonBit_bounds a x i).1
  · have h := Finset.sum_le_sum fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (singletonBit_bounds a x i).2
    simpa only [singletonCount, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one] using h

variable (μ : Fin n → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]

lemma integrable_singletonBit (a : ℝ) (i : Fin n) :
    Integrable (fun x => singletonBit a x i) (Measure.pi μ) := by
  apply Integrable.of_bound (measurable_singletonBit a i).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (singletonBit_bounds a x i).1]
    exact (singletonBit_bounds a x i).2

lemma integral_singletonBit (a : ℝ) (i : Fin n) :
    (∫ x, singletonBit a x i ∂Measure.pi μ) = (μ i).real {a} := by
  have hp := measurePreserving_eval μ i
  have hm : Measurable (fun v : ℝ => if v = a then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const
  have he := integral_map (μ := Measure.pi μ) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  have hsi := integral_indicator_const (μ := μ i) (1 : ℝ) (measurableSet_singleton a)
  have hscalar : (∫ v, if v = a then (1 : ℝ) else 0 ∂μ i) = (μ i).real {a} := by
    simpa only [Set.indicator_apply, Set.mem_singleton_iff, smul_eq_mul, mul_one] using hsi
  exact he.symm.trans hscalar

lemma integrable_singletonBit_product (a : ℝ) (i j : Fin n) :
    Integrable (fun x => singletonBit a x i * singletonBit a x j) (Measure.pi μ) := by
  apply Integrable.of_bound ((measurable_singletonBit a i).mul (measurable_singletonBit a j)).aestronglyMeasurable 1
  exact Eventually.of_forall fun x => by
    change ‖singletonBit a x i * singletonBit a x j‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (singletonBit_bounds a x i).1 (singletonBit_bounds a x j).1)]
    exact mul_le_one₀ (singletonBit_bounds a x i).2 (singletonBit_bounds a x j).1 (singletonBit_bounds a x j).2

lemma integral_singletonBit_product (a : ℝ) {i j : Fin n} (hij : i ≠ j) :
    (∫ x, singletonBit a x i * singletonBit a x j ∂Measure.pi μ) = (μ i).real {a} * (μ j).real {a} := by
  have hm : Measurable (fun v : ℝ => if v = a then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const
  have hind := ((iIndepFun_pi (μ := μ) (X := fun _ => id) (fun _ => aemeasurable_id)).indepFun hij).comp hm hm
  have he := hind.integral_fun_mul_eq_mul_integral (measurable_singletonBit a i).aestronglyMeasurable
    (measurable_singletonBit a j).aestronglyMeasurable
  change (∫ x, singletonBit a x i * singletonBit a x j ∂Measure.pi μ) =
    (∫ x, singletonBit a x i ∂Measure.pi μ) * (∫ x, singletonBit a x j ∂Measure.pi μ) at he
  rw [integral_singletonBit, integral_singletonBit] at he
  exact he

lemma integral_singletonCount (a : ℝ) :
    (∫ x, singletonCount a x ∂Measure.pi μ) = ∑ i, (μ i).real {a} := by
  unfold singletonCount
  rw [integral_finsetSum _ (fun i _ => integrable_singletonBit μ a i)]
  simp only [integral_singletonBit]

lemma integral_singletonCount_sq_le (a : ℝ) :
    (∫ x, singletonCount a x ^ 2 ∂Measure.pi μ) ≤ (∑ i, (μ i).real {a}) ^ 2 + ∑ i, (μ i).real {a} := by
  have heq : (fun x : Fin n → ℝ => singletonCount a x ^ 2) = fun x => ∑ i, ∑ j, singletonBit a x i * singletonBit a x j := by
    funext x
    unfold singletonCount
    rw [pow_two, Finset.sum_mul]
    simp only [Finset.mul_sum]
  have hI (i : Fin n) : Integrable (fun x => ∑ j, singletonBit a x i * singletonBit a x j) (Measure.pi μ) :=
    integrable_finsetSum _ (fun j _ => integrable_singletonBit_product μ a i j)
  rw [heq, integral_finsetSum _ (fun i _ => hI i)]
  calc
    _ = ∑ i, ∑ j, ∫ x, singletonBit a x i * singletonBit a x j ∂Measure.pi μ := by
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finsetSum _ (fun j _ => integrable_singletonBit_product μ a i j)
    _ ≤ ∑ i, ∑ j, ((μ i).real {a} * (μ j).real {a} + if i = j then (μ i).real {a} else 0) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      by_cases hij : i = j
      · subst j
        have hfun : (fun x => singletonBit a x i * singletonBit a x i) = fun x => singletonBit a x i := by
          funext x
          unfold singletonBit
          split_ifs <;> norm_num
        rw [hfun, integral_singletonBit]
        simp only [ite_true]
        nlinarith [sq_nonneg ((μ i).real {a})]
      · rw [integral_singletonBit_product μ a hij, if_neg hij, add_zero]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
        ← Finset.mul_sum, ← Finset.sum_mul, pow_two]

/-- The actual independent singleton count has at least two occurrences with
probability at least one sixth whenever its mean is at least two. -/
theorem singletonCount_probability_gt_one_ge_sixth (a : ℝ) (hr : 2 ≤ ∑ i, (μ i).real {a}) :
    (1 : ℝ) / 6 ≤ (Measure.pi μ).real {x | 1 < singletonCount a x} := by
  exact ProphetSecretary.Analysis.probability_gt_one_ge_sixth (Measure.pi μ) (singletonCount a)
    (Finset.measurable_sum _ (fun i _ => measurable_singletonBit a i)) (Nat.cast_nonneg n)
    (singletonCount_bounds a) (integral_singletonCount μ a) hr (integral_singletonCount_sq_le μ a)

end ProphetSecretary.Probability
