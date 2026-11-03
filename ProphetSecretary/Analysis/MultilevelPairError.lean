import ProphetSecretary.Analysis.MultilevelRawMean
import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Errors at a shared sampled child

The adjacent recursive estimates share their transition and hence their true
child value. Lipschitz continuity compares their difference with their two
squared errors. Uniform state bounds may then be integrated over the sampled
transition without any dependence assumption about that state.
-/

open MeasureTheory

namespace ProphetSecretary.Analysis

lemma lipschitz_pair_sq_le (f : ℝ → ℝ) (hf : LipschitzWith 1 f) (a b v : ℝ) :
    (f a - f b) ^ 2 ≤ 2 * ((a - v) ^ 2 + (b - v) ^ 2) := by
  have hd : |f a - f b| ≤ |a - b| := by
    simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using hf.dist_le_mul a b
  have hs := (sq_le_sq₀ (abs_nonneg (f a - f b)) (abs_nonneg (a - b))).2 hd
  simp only [sq_abs] at hs
  nlinarith [sq_nonneg (a + b - 2 * v)]

noncomputable def multilevelChildSqError {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition ℝ) (v : State → ℝ)
    (r : ℕ) (x : State) (q : Seed × MultilevelTree Seed r) : ℝ :=
  let child := D.child x (D.sample x q.1)
  (multilevelEstimate D r child q.2 - v child) ^ 2

lemma measurable_multilevelChildSqError {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (v : State → ℝ) (hv : Measurable v) (r : ℕ) (x : State) :
    Measurable (multilevelChildSqError D v r x) := by
  have hs : Measurable (fun q : Seed × MultilevelTree Seed r => D.sample x q.1) :=
    hD.sample.comp (measurable_const.prodMk measurable_fst)
  have hc : Measurable (fun q : Seed × MultilevelTree Seed r => D.child x (D.sample x q.1)) :=
    hD.child.comp (measurable_const.prodMk hs)
  exact (((measurable_multilevelEstimate D hD r).comp (hc.prodMk measurable_snd)).sub
    (hv.comp hc)).pow_const 2

lemma integrable_multilevelChildSqError {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (v : State → ℝ) (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State) :
    Integrable (multilevelChildSqError D v r x) (μ.prod (multilevelTreeLaw μ r)) := by
  apply Integrable.of_bound (measurable_multilevelChildSqError D hD v hv r x).aestronglyMeasurable 25
  exact ae_of_all _ (fun q => by
    dsimp only [multilevelChildSqError]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact multilevelEstimate_sq_error_le_twentyFive D hEmpty r
      (D.child x (D.sample x q.1)) q.2
      (hvb (D.child x (D.sample x q.1))).1 (hvb (D.child x (D.sample x q.1))).2)

/-- A squared-error bound uniform over deterministic states also holds at the
sampled child, because its recursive tree is independent of the transition. -/
lemma integral_multilevelChildSqError_le {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (v : State → ℝ) (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (E : ℝ)
    (hE : ∀ y, (∫ t, (multilevelEstimate D r y t - v y) ^ 2 ∂multilevelTreeLaw μ r) ≤ E)
    (x : State) : (∫ q, multilevelChildSqError D v r x q ∂μ.prod (multilevelTreeLaw μ r)) ≤ E := by
  have hi := integrable_multilevelChildSqError D hD hEmpty v hv hvb μ r x
  rw [integral_prod (multilevelChildSqError D v r x) hi]
  calc
    _ ≤ ∫ _s : Seed, E ∂μ :=
      integral_mono hi.integral_prod_left (integrable_const E) (fun s => hE (D.child x (D.sample x s)))
    _ = _ := by simp

lemma multilevelPairTerm_sq_le {State Seed Transition : Type*} [MeasurableSpace Seed]
    (D : MultilevelRecursion State Seed Transition ℝ)
    (hLip : ∀ x y, LipschitzWith 1 (D.payoff x y)) (v : State → ℝ)
    (r : ℕ) (x : State) (l : Fin r) (j : Fin (4 ^ (r - l.val)))
    (t : MultilevelTree Seed (r + 1)) :
    (multilevelPairTerm D r x l j t) ^ 2 ≤
      2 * (let d := multilevelNodeMeasurableEquiv Seed r t
        multilevelChildSqError D v (l.val + 1) x (d.2.1 l j, d.2.2.1 l j) +
          multilevelChildSqError D v l.val x (d.2.1 l j, d.2.2.2 l j)) := by
  exact lipschitz_pair_sq_le _ (hLip x _)
    (multilevelEstimate D (l.val + 1)
      (D.child x (D.sample x ((multilevelNodeMeasurableEquiv Seed r t).2.1 l j)))
      ((multilevelNodeMeasurableEquiv Seed r t).2.2.1 l j))
    (multilevelEstimate D l.val
      (D.child x (D.sample x ((multilevelNodeMeasurableEquiv Seed r t).2.1 l j)))
      ((multilevelNodeMeasurableEquiv Seed r t).2.2.2 l j))
    (v (D.child x (D.sample x ((multilevelNodeMeasurableEquiv Seed r t).2.1 l j))))

end ProphetSecretary.Analysis
