import ProphetSecretary.Analysis.MultilevelVarianceBound
import ProphetSecretary.Analysis.MultilevelBias
import ProphetSecretary.Analysis.MultilevelErrorEnvelope

/-!
# Mean-square accuracy of the actual multilevel estimator

The primitive callbacks specify a weighted fixed-point recursion. The finite
random-tree law, rather than an assumed moment recurrence, supplies the bias
and variance estimates. An explicit numerical envelope makes their uniformity
over states precise.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProphetSecretary.Analysis

theorem multilevel_mean_square_step {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hPay : ∀ x y w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x y w ∧ D.payoff x y w ≤ 1)
    (hLip : ∀ x y, LipschitzWith 1 (D.payoff x y))
    (v : State → ℝ) (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5)
    (hEmpty : ∀ x, D.isEmpty x = true → D.emptyValue x = v x)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (e : ℕ → ℝ)
    (he0 : ∀ k, 0 ≤ e k)
    (he : ∀ k, k ≤ r → ∀ y,
      (∫ t, (multilevelEstimate D k y t - v y) ^ 2 ∂multilevelTreeLaw μ k) ≤ e k)
    (x : State) (hc0 : 0 ≤ D.coefficient x) (hc1 : D.coefficient x ≤ 1/4)
    (hfix : D.isEmpty x = false → v x = D.offset x + D.coefficient x *
      ∫ s, D.payoff x (D.sample x s) (v (D.child x (D.sample x s))) ∂μ) :
    (∫ t, (multilevelEstimate D (r + 1) x t - v x) ^ 2 ∂multilevelTreeLaw μ (r + 1)) ≤
      (1 / 16 : ℝ) * (e r + (1 / 4 : ℝ) ^ (r + 1) +
        2 * ∑ l : Fin r, (1 / 4 : ℝ) ^ (r - l.val) * (e (l.val + 1) + e l.val)) := by
  have hEmptyBound : ∀ y, D.isEmpty y = true → 0 ≤ D.emptyValue y ∧ D.emptyValue y ≤ 5 := by
    intro y hy
    rw [hEmpty y hy]
    exact hvb y
  by_cases hx : D.isEmpty x = true
  · have hz : (fun t : MultilevelTree Seed (r + 1) =>
        (multilevelEstimate D (r + 1) x t - v x) ^ 2) = fun _ => 0 := by
      funext t
      rw [multilevelEstimate_empty D r x hx, hEmpty x hx]
      ring
    rw [hz, integral_zero]
    apply mul_nonneg (by norm_num)
    apply add_nonneg
    · exact add_nonneg (he0 r) (by positivity)
    · apply mul_nonneg (by norm_num)
      exact Finset.sum_nonneg (fun l _ =>
        mul_nonneg (by positivity) (add_nonneg (he0 _) (he0 _)))
  · have hfalse : D.isEmpty x = false := by cases h : D.isEmpty x <;> simp_all
    have hr : multilevelRawEstimate D r x =
        fun t => D.offset x + D.coefficient x * multilevelNoise D r x t := by
      funext t
      exact multilevelRawEstimate_eq_noise D r x t
    have hRaw : MemLp (multilevelRawEstimate D r x) 2 (multilevelTreeLaw μ (r + 1)) := by
      rw [hr]
      exact (memLp_const (D.offset x)).add
        ((memLp_multilevelNoise D hD hEmptyBound hPay μ r x).const_mul (D.coefficient x))
    have hvar := variance_eq_sub (hRaw.sub (memLp_const (v x)))
    change variance (fun t => multilevelRawEstimate D r x t - v x) (multilevelTreeLaw μ (r + 1)) =
      (∫ t, (multilevelRawEstimate D r x t - v x) ^ 2 ∂multilevelTreeLaw μ (r + 1)) -
        (∫ t, multilevelRawEstimate D r x t - v x ∂multilevelTreeLaw μ (r + 1)) ^ 2 at hvar
    rw [variance_sub_const hRaw.aestronglyMeasurable,
      integral_sub (hRaw.integrable (by norm_num)) (integrable_const (v x))] at hvar
    simp only [integral_const, probReal_univ, one_smul] at hvar
    have hclip := integral_mono
      (integrable_multilevelEstimate_sq_error D hD hEmptyBound μ (r + 1) x (hvb x).1 (hvb x).2)
      (hRaw.sub (memLp_const (v x))).integrable_sq
      (fun t => multilevelEstimate_sq_error_le_raw D r x hfalse t (hvb x).1 (hvb x).2)
    have hb := multilevelRawEstimate_sq_bias_le D hD hEmptyBound hPay hLip v hv hvb μ r
      (e r) (he r le_rfl) x hc0 hc1 (hfix hfalse)
    have hv' := variance_multilevelRawEstimate_le D hD hEmptyBound hPay hLip v hv hvb μ r
      e he0 he x hc0 hc1
    simp only [Pi.sub_apply] at hclip
    nlinarith

/-- `alg:mlmc-rate` for the actual finite-tree estimator of a weighted
fixed-point problem. The scalar-planning instance must supply its primitive
callbacks and prove the displayed fixed-point equation. -/
theorem integral_multilevelEstimate_sq_error_le {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hPay : ∀ x y w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x y w ∧ D.payoff x y w ≤ 1)
    (hLip : ∀ x y, LipschitzWith 1 (D.payoff x y))
    (v : State → ℝ) (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5)
    (hEmpty : ∀ x, D.isEmpty x = true → D.emptyValue x = v x)
    (μ : Measure Seed) [IsProbabilityMeasure μ]
    (hc : ∀ x, 0 ≤ D.coefficient x ∧ D.coefficient x ≤ 1/4)
    (hfix : ∀ x, D.isEmpty x = false → v x = D.offset x + D.coefficient x *
      ∫ s, D.payoff x (D.sample x s) (v (D.child x (D.sample x s))) ∂μ)
    (r : ℕ) (x : State) :
    (∫ t, (multilevelEstimate D r x t - v x) ^ 2 ∂multilevelTreeLaw μ r) ≤
      25 * (1 / 2 : ℝ) ^ r := by
  have hEnv : ∀ k : ℕ, ∀ y : State,
      (∫ t, (multilevelEstimate D k y t - v y) ^ 2 ∂multilevelTreeLaw μ k) ≤
        multilevelErrorEnvelope k := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro y
      cases k with
      | zero =>
        have hEmptyBound : ∀ z, D.isEmpty z = true → 0 ≤ D.emptyValue z ∧ D.emptyValue z ≤ 5 := by
          intro z hz
          rw [hEmpty z hz]
          exact hvb z
        rw [multilevelErrorEnvelope]
        exact integral_multilevelEstimate_sq_error_le_twentyFive D hD hEmptyBound μ 0 y
          (hvb y).1 (hvb y).2
      | succ n =>
        rw [multilevelErrorEnvelope]
        exact multilevel_mean_square_step D hD hPay hLip v hv hvb hEmpty μ n
          multilevelErrorEnvelope multilevelErrorEnvelope_nonnegative
          (fun j hj z => ih j (by omega) z) y (hc y).1 (hc y).2 (hfix y)
  exact (hEnv r x).trans (multilevelErrorEnvelope_decay r)

end ProphetSecretary.Analysis
