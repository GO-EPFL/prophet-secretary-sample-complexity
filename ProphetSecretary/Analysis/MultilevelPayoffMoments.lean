import ProphetSecretary.Analysis.MultilevelRawEstimate

/-!
# The expected payoff of an adjacent-level pair

The expectation uses the constructed finite tree law and the same transition
seed for the upper and lower evaluation. Bounds on primitive payoffs give
the integrability needed for telescoping the estimator's raw mean.
-/

open MeasureTheory

namespace ProphetSecretary.Analysis

def multilevelPayoffEstimate {Value State Seed Transition : Type*} [Field Value]
    [LinearOrder Value] (D : MultilevelRecursion State Seed Transition Value)
    (r : ℕ) (x : State) (q : Seed × MultilevelTree Seed r) : Value :=
  let y := D.sample x q.1
  D.payoff x y (multilevelEstimate D r (D.child x y) q.2)

lemma measurable_multilevelPayoffEstimate {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (r : ℕ) (x : State) : Measurable (multilevelPayoffEstimate D r x) := by
  have hs : Measurable (fun q : Seed × MultilevelTree Seed r => D.sample x q.1) :=
    hD.sample.comp (measurable_const.prodMk measurable_fst)
  have hc : Measurable (fun q : Seed × MultilevelTree Seed r => D.child x (D.sample x q.1)) :=
    hD.child.comp (measurable_const.prodMk hs)
  have he := (measurable_multilevelEstimate D hD r).comp (hc.prodMk measurable_snd)
  exact hD.payoff.comp ((measurable_const.prodMk hs).prodMk he)

lemma multilevelPayoffEstimate_bounds {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition ℝ)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y v, 0 ≤ v → v ≤ 5 → 0 ≤ D.payoff x y v ∧ D.payoff x y v ≤ 1)
    (r : ℕ) (x : State) (q : Seed × MultilevelTree Seed r) :
    0 ≤ multilevelPayoffEstimate D r x q ∧ multilevelPayoffEstimate D r x q ≤ 1 := by
  have hb := multilevelEstimate_bounds D hEmpty r (D.child x (D.sample x q.1)) q.2
  exact hPay x (D.sample x q.1) _ hb.1 hb.2

lemma integrable_multilevelPayoffEstimate {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y v, 0 ≤ v → v ≤ 5 → 0 ≤ D.payoff x y v ∧ D.payoff x y v ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State) :
    Integrable (multilevelPayoffEstimate D r x) (μ.prod (multilevelTreeLaw μ r)) := by
  apply Integrable.of_bound (measurable_multilevelPayoffEstimate D hD r x).aestronglyMeasurable 1
  exact ae_of_all _ (fun q => by
    rw [Real.norm_eq_abs, abs_of_nonneg (multilevelPayoffEstimate_bounds D hEmpty hPay r x q).1]
    exact (multilevelPayoffEstimate_bounds D hEmpty hPay r x q).2)

noncomputable def multilevelExpectedPayoff {State Seed Transition : Type*}
    [MeasurableSpace Seed] (D : MultilevelRecursion State Seed Transition ℝ)
    (μ : Measure Seed) (r : ℕ) (x : State) : ℝ :=
  ∫ q, multilevelPayoffEstimate D r x q ∂μ.prod (multilevelTreeLaw μ r)

lemma multilevelExpectedPayoff_zero {State Seed Transition : Type*}
    [MeasurableSpace Seed] (D : MultilevelRecursion State Seed Transition ℝ)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (x : State) :
    multilevelExpectedPayoff D μ 0 x = ∫ s, D.payoff x (D.sample x s) 0 ∂μ := by
  unfold multilevelExpectedPayoff
  have hfun : (fun q : Seed × MultilevelTree Seed 0 => multilevelPayoffEstimate D 0 x q) =
      fun q => D.payoff x (D.sample x q.1) 0 := by
    funext q
    simp [multilevelPayoffEstimate, multilevelEstimate_zero]
  rw [hfun]
  simpa using integral_fun_fst (μ := μ) (ν := multilevelTreeLaw μ 0)
    (fun s => D.payoff x (D.sample x s) 0)

lemma integral_multilevelPair_payoff_sub {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y v, 0 ≤ v → v ≤ 5 → 0 ≤ D.payoff x y v ∧ D.payoff x y v ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (l : Fin r)
    (j : Fin (4 ^ (r - l.val))) (x : State) :
    (∫ t, (let d := multilevelNodeMeasurableEquiv Seed r t
      let y := D.sample x (d.2.1 l j)
      let child := D.child x y
      D.payoff x y (multilevelEstimate D (l.val + 1) child (d.2.2.1 l j)) -
        D.payoff x y (multilevelEstimate D l.val child (d.2.2.2 l j)))
        ∂multilevelTreeLaw μ (r + 1)) =
      multilevelExpectedPayoff D μ (l.val + 1) x - multilevelExpectedPayoff D μ l.val x := by
  exact integral_multilevelPair_sub μ r l j
    (multilevelPayoffEstimate D (l.val + 1) x) (multilevelPayoffEstimate D l.val x)
    (integrable_multilevelPayoffEstimate D hD hEmpty hPay μ (l.val + 1) x)
    (integrable_multilevelPayoffEstimate D hD hEmpty hPay μ l.val x)

end ProphetSecretary.Analysis
