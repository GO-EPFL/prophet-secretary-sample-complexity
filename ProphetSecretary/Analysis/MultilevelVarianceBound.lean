import ProphetSecretary.Analysis.MultilevelVariance

/-! # Quantitative variance in the multilevel mean-square recurrence -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace ProphetSecretary.Analysis

lemma multilevel_average_square (k : ℕ) :
    (4 : ℝ) ^ k * (1 / ((4 : ℝ) ^ k)) ^ 2 = (1 / 4 : ℝ) ^ k := by
  have hp : (4 : ℝ) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
  simp only [one_div_pow]
  field_simp

lemma variance_multilevelBaseTerm_le_one {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x y w ∧ D.payoff x y w ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State) (j : Fin (4 ^ (r + 1))) :
    variance (multilevelBaseTerm D r x j) (multilevelTreeLaw μ (r + 1)) ≤ 1 := by
  have hm := memLp_multilevelSummandTerm D hD hEmpty hPay μ r x (.inl j)
  calc
    _ ≤ ∫ t, (multilevelBaseTerm D r x j t) ^ 2 ∂multilevelTreeLaw μ (r + 1) :=
      variance_le_expectation_sq hm.aestronglyMeasurable
    _ ≤ ∫ _t : MultilevelTree Seed (r + 1), (1 : ℝ) ∂multilevelTreeLaw μ (r + 1) := by
      apply integral_mono hm.integrable_sq (integrable_const 1)
      intro t
      have hb := norm_multilevelSummandTerm_le_one D hEmpty hPay r x (.inl j) t
      rw [Real.norm_eq_abs] at hb
      have hs := (sq_le_sq₀ (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)).2 hb
      simpa only [sq_abs, one_pow] using hs
    _ = _ := by simp

/-- The exact variance sum has the coefficients in `alg:mlmc-mse`. -/
theorem variance_multilevelRawEstimate_le {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x y w ∧ D.payoff x y w ≤ 1)
    (hLip : ∀ x y, LipschitzWith 1 (D.payoff x y))
    (v : State → ℝ) (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (e : ℕ → ℝ)
    (he0 : ∀ k, 0 ≤ e k)
    (he : ∀ k, k ≤ r → ∀ y,
      (∫ t, (multilevelEstimate D k y t - v y) ^ 2 ∂multilevelTreeLaw μ k) ≤ e k)
    (x : State) (hc0 : 0 ≤ D.coefficient x) (hc1 : D.coefficient x ≤ 1/4) :
    variance (multilevelRawEstimate D r x) (multilevelTreeLaw μ (r + 1)) ≤
      (1 / 16 : ℝ) * ((1 / 4 : ℝ) ^ (r + 1) +
        2 * ∑ l : Fin r, (1 / 4 : ℝ) ^ (r - l.val) * (e (l.val + 1) + e l.val)) := by
  have hPair (l : Fin r) (j : Fin (4 ^ (r - l.val))) :
      variance (multilevelPairTerm D r x l j) (multilevelTreeLaw μ (r + 1)) ≤
        2 * (e (l.val + 1) + e l.val) := by
    have hm := memLp_multilevelSummandTerm D hD hEmpty hPay μ r x (.inr ⟨l, j⟩)
    exact (variance_le_expectation_sq hm.aestronglyMeasurable).trans
      (integral_multilevelPairTerm_sq_le D hD hEmpty hPay hLip v hv hvb μ r l
        (e (l.val + 1)) (e l.val) (he _ (by have := l.isLt; omega))
        (he _ (by have := l.isLt; omega)) x j)
  have hsum : (∑ i : MultilevelSummandIndex r, (multilevelSummandWeight r i) ^ 2 *
      variance (multilevelSummandTerm D r x i) (multilevelTreeLaw μ (r + 1))) ≤
        (1 / 4 : ℝ) ^ (r + 1) +
          2 * ∑ l : Fin r, (1 / 4 : ℝ) ^ (r - l.val) * (e (l.val + 1) + e l.val) := by
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    apply add_le_add
    · calc
        _ ≤ ∑ _j : Fin (4 ^ (r + 1)), (1 / ((4 : ℝ) ^ (r + 1))) ^ 2 := by
          apply Finset.sum_le_sum
          intro j _
          have hb := variance_multilevelBaseTerm_le_one D hD hEmpty hPay μ r x j
          exact mul_le_of_le_one_right (sq_nonneg _) hb
        _ = _ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
          exact multilevel_average_square (r + 1)
    · calc
        _ ≤ ∑ l : Fin r, ∑ _j : Fin (4 ^ (r - l.val)),
            (1 / ((4 : ℝ) ^ (r - l.val))) ^ 2 * 2 * (e (l.val + 1) + e l.val) := by
          apply Finset.sum_le_sum
          intro l _
          apply Finset.sum_le_sum
          intro j _
          have hp := mul_le_mul_of_nonneg_left (hPair l j)
            (sq_nonneg (1 / ((4 : ℝ) ^ (r - l.val))))
          simpa only [multilevelSummandWeight, multilevelSummandTerm, mul_assoc] using hp
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro l _
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
            nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
          calc
            _ = 2 * ((4 : ℝ) ^ (r - l.val) * (1 / ((4 : ℝ) ^ (r - l.val))) ^ 2) *
                (e (l.val + 1) + e l.val) := by ring
            _ = _ := by rw [multilevel_average_square]; ring
  have hB : 0 ≤ (1 / 4 : ℝ) ^ (r + 1) +
      2 * ∑ l : Fin r, (1 / 4 : ℝ) ^ (r - l.val) * (e (l.val + 1) + e l.val) := by
    apply add_nonneg (by positivity)
    apply mul_nonneg (by norm_num)
    exact Finset.sum_nonneg (fun l _ => mul_nonneg (by positivity) (add_nonneg (he0 _) (he0 _)))
  have hcSq : (D.coefficient x) ^ 2 ≤ 1/16 := by nlinarith
  rw [variance_multilevelRawEstimate D hD hEmpty hPay μ r x]
  exact (mul_le_mul_of_nonneg_left hsum (sq_nonneg (D.coefficient x))).trans
    (mul_le_mul_of_nonneg_right hcSq hB)

end ProphetSecretary.Analysis
