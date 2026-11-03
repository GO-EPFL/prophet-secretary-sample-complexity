import ProphetSecretary.Analysis.MultilevelSummandIndependence
import ProphetSecretary.Analysis.MultilevelPairSecondMoment
import Mathlib.Probability.Moments.Variance

/-!
# Variance of the actual multilevel estimator

Pairwise independence is obtained from the disjoint primitive coordinates
of the constructed random tree. The variance therefore sums over all base
and paired samples, with their actual averaging coefficients.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProphetSecretary.Analysis

noncomputable def multilevelSummandWeight (r : ℕ) : MultilevelSummandIndex r → ℝ
  | .inl _ => 1 / ((4 : ℝ) ^ (r + 1))
  | .inr q => 1 / ((4 : ℝ) ^ (r - q.1.val))

noncomputable def multilevelNoise {State Seed Transition : Type*} [MeasurableSpace Seed]
    (D : MultilevelRecursion State Seed Transition ℝ) (r : ℕ) (x : State)
    (t : MultilevelTree Seed (r + 1)) : ℝ :=
  ∑ i : MultilevelSummandIndex r, multilevelSummandWeight r i * multilevelSummandTerm D r x i t

lemma multilevelRawEstimate_eq_noise {State Seed Transition : Type*} [MeasurableSpace Seed]
    (D : MultilevelRecursion State Seed Transition ℝ) (r : ℕ) (x : State)
    (t : MultilevelTree Seed (r + 1)) :
    multilevelRawEstimate D r x t = D.offset x + D.coefficient x * multilevelNoise D r x t := by
  simp [multilevelNoise, Fintype.sum_sum_type, Fintype.sum_sigma, multilevelSummandWeight,
    multilevelSummandTerm, multilevelBaseTerm, multilevelPairTerm,
    multilevelPayoffEstimate, multilevelRawEstimate, multilevelNodeMeasurableEquiv,
    Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]

lemma norm_multilevelSummandTerm_le_one {State Seed Transition : Type*} [MeasurableSpace Seed]
    (D : MultilevelRecursion State Seed Transition ℝ)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x y w ∧ D.payoff x y w ≤ 1)
    (r : ℕ) (x : State) (i : MultilevelSummandIndex r) (t : MultilevelTree Seed (r + 1)) :
    ‖multilevelSummandTerm D r x i t‖ ≤ 1 := by
  rcases i with b | q
  · have hb := hPay x (D.sample x ((multilevelNodeMeasurableEquiv Seed r t).1 b))
      0 le_rfl (by norm_num)
    change ‖D.payoff x (D.sample x ((multilevelNodeMeasurableEquiv Seed r t).1 b)) 0‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2
  · let d := multilevelNodeMeasurableEquiv Seed r t
    have hu := multilevelPayoffEstimate_bounds D hEmpty hPay (q.1.val + 1) x
      (d.2.1 q.1 q.2, d.2.2.1 q.1 q.2)
    have hl := multilevelPayoffEstimate_bounds D hEmpty hPay q.1.val x
      (d.2.1 q.1 q.2, d.2.2.2 q.1 q.2)
    change ‖multilevelPayoffEstimate D (q.1.val + 1) x (d.2.1 q.1 q.2, d.2.2.1 q.1 q.2) -
      multilevelPayoffEstimate D q.1.val x (d.2.1 q.1 q.2, d.2.2.2 q.1 q.2)‖ ≤ 1
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hu.1, hu.2, hl.1, hl.2],
      by linarith [hu.1, hu.2, hl.1, hl.2]⟩

lemma memLp_multilevelSummandTerm {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x y w ∧ D.payoff x y w ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State)
    (i : MultilevelSummandIndex r) :
    MemLp (multilevelSummandTerm D r x i) 2 (multilevelTreeLaw μ (r + 1)) := by
  have hi : Integrable (multilevelSummandTerm D r x i) (multilevelTreeLaw μ (r + 1)) := by
    rcases i with b | q
    · exact integrable_multilevelBaseTerm D hD hPay μ r x b
    · exact integrable_multilevelPairTerm D hD hEmpty hPay μ r x q.1 q.2
  exact MemLp.of_bound hi.aestronglyMeasurable 1
    (ae_of_all _ (norm_multilevelSummandTerm_le_one D hEmpty hPay r x i))

lemma memLp_multilevelNoise {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x y w ∧ D.payoff x y w ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State) :
    MemLp (multilevelNoise D r x) 2 (multilevelTreeLaw μ (r + 1)) := by
  exact memLp_finsetSum Finset.univ (fun i _ =>
    (memLp_multilevelSummandTerm D hD hEmpty hPay μ r x i).const_mul (multilevelSummandWeight r i))

theorem variance_multilevelRawEstimate {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x y w ∧ D.payoff x y w ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State) :
    variance (multilevelRawEstimate D r x) (multilevelTreeLaw μ (r + 1)) =
      (D.coefficient x) ^ 2 * ∑ i : MultilevelSummandIndex r,
        (multilevelSummandWeight r i) ^ 2 *
          variance (multilevelSummandTerm D r x i) (multilevelTreeLaw μ (r + 1)) := by
  have hL (i : MultilevelSummandIndex r) :=
    (memLp_multilevelSummandTerm D hD hEmpty hPay μ r x i).const_mul (multilevelSummandWeight r i)
  have hInd (i j : MultilevelSummandIndex r) (hij : i ≠ j) :
      IndepFun (fun t => multilevelSummandWeight r i * multilevelSummandTerm D r x i t)
        (fun t => multilevelSummandWeight r j * multilevelSummandTerm D r x j t)
        (multilevelTreeLaw μ (r + 1)) :=
    (multilevelSummandTerm_indepFun D hD μ r x i j hij).comp
      (measurable_const.mul measurable_id) (measurable_const.mul measurable_id)
  have hv := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hL i)
    (fun i _ j _ hij => hInd i j hij)
  have hn : variance (multilevelNoise D r x) (multilevelTreeLaw μ (r + 1)) =
      ∑ i : MultilevelSummandIndex r, (multilevelSummandWeight r i) ^ 2 *
        variance (multilevelSummandTerm D r x i) (multilevelTreeLaw μ (r + 1)) := by
    have hf : (∑ i : MultilevelSummandIndex r,
        fun t => multilevelSummandWeight r i * multilevelSummandTerm D r x i t) =
        multilevelNoise D r x := by
      funext t
      simp [multilevelNoise]
    rw [hf] at hv
    simpa only [variance_const_mul] using hv
  have hr : multilevelRawEstimate D r x =
      fun t => D.offset x + D.coefficient x * multilevelNoise D r x t := by
    funext t
    exact multilevelRawEstimate_eq_noise D r x t
  rw [hr, variance_const_add
    ((memLp_multilevelNoise D hD hEmpty hPay μ r x).const_mul _).aestronglyMeasurable,
    variance_const_mul, hn]

end ProphetSecretary.Analysis
