import ProphetSecretary.Analysis.MultilevelPairError
import ProphetSecretary.Analysis.SumIntegralCauchy

/-!
# Squared bias of the actual multilevel estimate

The expected raw estimate is the weighted one-step recursion applied to the
preceding random level. A shared sampled child, Lipschitz continuity and
Cauchy--Schwarz turn a uniform mean-square child error into squared bias.
-/

open MeasureTheory

namespace ProphetSecretary.Analysis

lemma multilevelExpectedPayoff_sq_error_le {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y t, 0 ≤ t → t ≤ 5 → 0 ≤ D.payoff x y t ∧ D.payoff x y t ≤ 1)
    (hLip : ∀ x y, LipschitzWith 1 (D.payoff x y))
    (v : State → ℝ) (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (E : ℝ)
    (hE : ∀ y, (∫ t, (multilevelEstimate D r y t - v y) ^ 2 ∂multilevelTreeLaw μ r) ≤ E)
    (x : State) :
    (multilevelExpectedPayoff D μ r x -
      ∫ s, D.payoff x (D.sample x s) (v (D.child x (D.sample x s))) ∂μ) ^ 2 ≤ E := by
  let g : Seed × MultilevelTree Seed r → ℝ := fun q =>
    multilevelPayoffEstimate D r x q -
      D.payoff x (D.sample x q.1) (v (D.child x (D.sample x q.1)))
  have hs : Measurable (fun q : Seed × MultilevelTree Seed r => D.sample x q.1) :=
    hD.sample.comp (measurable_const.prodMk measurable_fst)
  have hc : Measurable (fun q : Seed × MultilevelTree Seed r => D.child x (D.sample x q.1)) :=
    hD.child.comp (measurable_const.prodMk hs)
  have ht : Measurable (fun q : Seed × MultilevelTree Seed r =>
      D.payoff x (D.sample x q.1) (v (D.child x (D.sample x q.1)))) :=
    hD.payoff.comp ((measurable_const.prodMk hs).prodMk (hv.comp hc))
  have hgm : Measurable g := (measurable_multilevelPayoffEstimate D hD r x).sub ht
  have hgBound (q : Seed × MultilevelTree Seed r) : ‖g q‖ ≤ 1 := by
    have he := multilevelPayoffEstimate_bounds D hEmpty hPay r x q
    have he' := hPay x (D.sample x q.1) (v (D.child x (D.sample x q.1)))
      (hvb (D.child x (D.sample x q.1))).1 (hvb (D.child x (D.sample x q.1))).2
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by dsimp only [g]; linarith [he.1, he.2, he'.1, he'.2],
      by dsimp only [g]; linarith [he.1, he.2, he'.1, he'.2]⟩
  have hgL2 : MemLp g 2 (μ.prod (multilevelTreeLaw μ r)) :=
    MemLp.of_bound hgm.aestronglyMeasurable 1 (ae_of_all _ hgBound)
  have htInt : Integrable (fun q : Seed × MultilevelTree Seed r =>
      D.payoff x (D.sample x q.1) (v (D.child x (D.sample x q.1))))
      (μ.prod (multilevelTreeLaw μ r)) := by
    apply Integrable.of_bound ht.aestronglyMeasurable 1
    exact ae_of_all _ (fun q => by
      have hb := hPay x (D.sample x q.1) (v (D.child x (D.sample x q.1)))
        (hvb (D.child x (D.sample x q.1))).1 (hvb (D.child x (D.sample x q.1))).2
      rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
      exact hb.2)
  have hmean : (∫ q, g q ∂μ.prod (multilevelTreeLaw μ r)) =
      multilevelExpectedPayoff D μ r x -
        ∫ s, D.payoff x (D.sample x s) (v (D.child x (D.sample x s))) ∂μ := by
    change (∫ q, multilevelPayoffEstimate D r x q -
      D.payoff x (D.sample x q.1) (v (D.child x (D.sample x q.1)))
        ∂μ.prod (multilevelTreeLaw μ r)) = _
    rw [integral_sub (integrable_multilevelPayoffEstimate D hD hEmpty hPay μ r x) htInt]
    congr 1
    simpa using integral_fun_fst (μ := μ) (ν := multilevelTreeLaw μ r)
      (fun s => D.payoff x (D.sample x s) (v (D.child x (D.sample x s))))
  have hj := sum_integral_mul_sq_le (ι := Unit)
    (fun _ => μ.prod (multilevelTreeLaw μ r)) (fun _ => g)
    (fun _ => fun _ => (1 : ℝ)) (fun _ => hgL2) (fun _ => memLp_const 1)
  have hJensen : (∫ q, g q ∂μ.prod (multilevelTreeLaw μ r)) ^ 2 ≤
      ∫ q, (g q) ^ 2 ∂μ.prod (multilevelTreeLaw μ r) := by
    simpa only [Fintype.sum_unique, mul_one, one_pow, integral_const,
      probReal_univ, one_smul] using hj
  have hpoint (q : Seed × MultilevelTree Seed r) :
      (g q) ^ 2 ≤ multilevelChildSqError D v r x q := by
    have hd := (hLip x (D.sample x q.1)).dist_le_mul
      (multilevelEstimate D r (D.child x (D.sample x q.1)) q.2)
      (v (D.child x (D.sample x q.1)))
    have ha : |g q| ≤ |multilevelEstimate D r (D.child x (D.sample x q.1)) q.2 -
        v (D.child x (D.sample x q.1))| := by
      simpa only [Real.dist_eq, NNReal.coe_one, one_mul, g, multilevelPayoffEstimate] using hd
    have hsq := (sq_le_sq₀ (abs_nonneg (g q)) (abs_nonneg _)).2 ha
    simpa only [sq_abs, multilevelChildSqError] using hsq
  have he := (integral_mono hgL2.integrable_sq
    (integrable_multilevelChildSqError D hD hEmpty v hv hvb μ r x) hpoint).trans
      (integral_multilevelChildSqError_le D hD hEmpty v hv hvb μ r E hE x)
  rw [← hmean]
  exact hJensen.trans he

/-- The `1/16` squared-bias factor for the actual raw estimator. The
fixed-point identity is a hypothesis of this general recursion theorem. -/
theorem multilevelRawEstimate_sq_bias_le {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y t, 0 ≤ t → t ≤ 5 → 0 ≤ D.payoff x y t ∧ D.payoff x y t ≤ 1)
    (hLip : ∀ x y, LipschitzWith 1 (D.payoff x y))
    (v : State → ℝ) (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (E : ℝ)
    (hE : ∀ y, (∫ t, (multilevelEstimate D r y t - v y) ^ 2 ∂multilevelTreeLaw μ r) ≤ E)
    (x : State) (hc0 : 0 ≤ D.coefficient x) (hc1 : D.coefficient x ≤ 1/4)
    (hfix : v x = D.offset x + D.coefficient x *
      ∫ s, D.payoff x (D.sample x s) (v (D.child x (D.sample x s))) ∂μ) :
    ((∫ t, multilevelRawEstimate D r x t ∂multilevelTreeLaw μ (r + 1)) - v x) ^ 2 ≤ E/16 := by
  have he := multilevelExpectedPayoff_sq_error_le D hD hEmpty hPay hLip v hv hvb μ r E hE x
  have hE0 : 0 ≤ E := (integral_nonneg (fun _ => sq_nonneg _)).trans (hE x)
  have hcSq : (D.coefficient x) ^ 2 ≤ 1/16 := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left he (sq_nonneg (D.coefficient x))
  have hbound := mul_le_mul_of_nonneg_right hcSq hE0
  rw [integral_multilevelRawEstimate D hD hEmpty hPay μ r x, hfix]
  nlinarith

end ProphetSecretary.Analysis
