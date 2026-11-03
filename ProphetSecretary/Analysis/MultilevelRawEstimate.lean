import ProphetSecretary.Analysis.MultilevelEstimatorMoments

/-!
# Raw multilevel estimates and their summand integrals

The transition and both child trees in a paired summand have the product law
proved for the actual finite random tree. These identities permit integration
of a summand before summing the multilevel differences.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Analysis

private lemma integral_comp_preserving {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {μ : Measure Ω} {ν : Measure Ω'} {p : Ω → Ω'}
    (hp : MeasurePreserving p μ ν) (f : Ω' → ℝ) (hf : AEStronglyMeasurable f ν) :
    (∫ q, f (p q) ∂μ) = ∫ q, f q ∂ν := by
  have hm : AEStronglyMeasurable f (Measure.map p μ) := by rw [hp.map_eq]; exact hf
  have hi := (integral_map hp.measurable.aemeasurable hm).symm
  rw [hp.map_eq] at hi
  exact hi

lemma integral_multilevelBase {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (j : Fin (4 ^ (r + 1)))
    (f : Seed → ℝ) (hf : AEStronglyMeasurable f μ) :
    (∫ t, f ((multilevelNodeMeasurableEquiv Seed r t).1 j) ∂multilevelTreeLaw μ (r + 1)) =
      ∫ s, f s ∂μ := by
  have hp := multilevelBase_measurePreserving μ r j
  have hm : AEStronglyMeasurable f
      (Measure.map (fun t : MultilevelTree Seed (r + 1) =>
        (multilevelNodeMeasurableEquiv Seed r t).1 j) (multilevelTreeLaw μ (r + 1))) := by
    rw [hp.map_eq]
    exact hf
  have hi := (integral_map hp.measurable.aemeasurable hm).symm
  rw [hp.map_eq] at hi
  exact hi

lemma integral_multilevelPair {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (l : Fin r)
    (j : Fin (4 ^ (r - l.val)))
    (f : Seed × (MultilevelTree Seed (l.val + 1) × MultilevelTree Seed l.val) → ℝ)
    (hf : AEStronglyMeasurable f
      (μ.prod ((multilevelTreeLaw μ (l.val + 1)).prod (multilevelTreeLaw μ l.val)))) :
    (∫ t, f (let d := multilevelNodeMeasurableEquiv Seed r t
      (d.2.1 l j, (d.2.2.1 l j, d.2.2.2 l j))) ∂multilevelTreeLaw μ (r + 1)) =
      ∫ q, f q ∂μ.prod ((multilevelTreeLaw μ (l.val + 1)).prod (multilevelTreeLaw μ l.val)) := by
  have hp := multilevelPair_measurePreserving μ r l j
  have hm : AEStronglyMeasurable f
      (Measure.map (fun t : MultilevelTree Seed (r + 1) =>
        let d := multilevelNodeMeasurableEquiv Seed r t
        (d.2.1 l j, (d.2.2.1 l j, d.2.2.2 l j))) (multilevelTreeLaw μ (r + 1))) := by
    rw [hp.map_eq]
    exact hf
  have hi := (integral_map hp.measurable.aemeasurable hm).symm
  rw [hp.map_eq] at hi
  exact hi

/-- Integrating a paired difference gives the difference of the adjacent
levels' means. The transition is shared, not resampled for the second copy. -/
lemma integral_multilevelPair_sub {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (l : Fin r)
    (j : Fin (4 ^ (r - l.val)))
    (f : Seed × MultilevelTree Seed (l.val + 1) → ℝ)
    (g : Seed × MultilevelTree Seed l.val → ℝ)
    (hf : Integrable f (μ.prod (multilevelTreeLaw μ (l.val + 1))))
    (hg : Integrable g (μ.prod (multilevelTreeLaw μ l.val))) :
    (∫ t, (let d := multilevelNodeMeasurableEquiv Seed r t
      f (d.2.1 l j, d.2.2.1 l j) - g (d.2.1 l j, d.2.2.2 l j))
        ∂multilevelTreeLaw μ (r + 1)) =
      (∫ q, f q ∂μ.prod (multilevelTreeLaw μ (l.val + 1))) -
        ∫ q, g q ∂μ.prod (multilevelTreeLaw μ l.val) := by
  have hu : MeasurePreserving
      (fun q : Seed × (MultilevelTree Seed (l.val + 1) × MultilevelTree Seed l.val) =>
        (q.1, q.2.1))
      (μ.prod ((multilevelTreeLaw μ (l.val + 1)).prod (multilevelTreeLaw μ l.val)))
      (μ.prod (multilevelTreeLaw μ (l.val + 1))) :=
    (MeasurePreserving.id μ).prod measurePreserving_fst
  have hl : MeasurePreserving
      (fun q : Seed × (MultilevelTree Seed (l.val + 1) × MultilevelTree Seed l.val) =>
        (q.1, q.2.2))
      (μ.prod ((multilevelTreeLaw μ (l.val + 1)).prod (multilevelTreeLaw μ l.val)))
      (μ.prod (multilevelTreeLaw μ l.val)) :=
    (MeasurePreserving.id μ).prod measurePreserving_snd
  have htu := hu.comp (multilevelPair_measurePreserving μ r l j)
  have htl := hl.comp (multilevelPair_measurePreserving μ r l j)
  have hfu := htu.integrable_comp_of_integrable hf
  have hgl := htl.integrable_comp_of_integrable hg
  have hiu := integral_comp_preserving htu f hf.aestronglyMeasurable
  have hil := integral_comp_preserving htl g hg.aestronglyMeasurable
  dsimp only [Function.comp_def] at hfu hgl hiu hil ⊢
  rw [integral_sub hfu hgl]
  rw [hiu, hil]

/-- The raw, unprojected estimate. Empty states use a separate exact return
in the actual estimator; this formula is used for nonempty states. -/
def multilevelRawEstimate {Value State Seed Transition : Type*} [Field Value] [LinearOrder Value]
    (D : MultilevelRecursion State Seed Transition Value) (r : ℕ) (x : State)
    (t : MultilevelTree Seed (r + 1)) : Value :=
  let d := multilevelNodeEquiv Seed r t
  D.offset x + D.coefficient x *
    ((1 / ((4 : Value) ^ (r + 1))) *
        ∑ j : Fin (4 ^ (r + 1)), D.payoff x (D.sample x (d.1 j)) 0 +
      ∑ l : Fin r, (1 / ((4 : Value) ^ (r - l.val))) *
        ∑ j : Fin (4 ^ (r - l.val)),
          let y := D.sample x (d.2.1 l j)
          let child := D.child x y
          D.payoff x y (multilevelEstimate D (l.val + 1) child (d.2.2.1 l j)) -
            D.payoff x y (multilevelEstimate D l.val child (d.2.2.2 l j)))

lemma multilevelEstimate_eq_clip_raw {Value State Seed Transition : Type*}
    [Field Value] [LinearOrder Value] (D : MultilevelRecursion State Seed Transition Value)
    (r : ℕ) (x : State) (hx : D.isEmpty x = false) (t : MultilevelTree Seed (r + 1)) :
    multilevelEstimate D (r + 1) x t = clipFive (multilevelRawEstimate D r x t) := by
  cases t
  simp [multilevelEstimate, multilevelRawEstimate, multilevelNodeEquiv, hx]

lemma multilevelEstimate_sq_error_le_raw {State Seed Transition : Type*}
    (D : MultilevelRecursion State Seed Transition ℝ) (r : ℕ) (x : State)
    (hx : D.isEmpty x = false) (t : MultilevelTree Seed (r + 1)) {v : ℝ}
    (hv0 : 0 ≤ v) (hv5 : v ≤ 5) :
    (multilevelEstimate D (r + 1) x t - v) ^ 2 ≤ (multilevelRawEstimate D r x t - v) ^ 2 := by
  rw [multilevelEstimate_eq_clip_raw D r x hx t]
  exact clipFive_sq_error_le _ hv0 hv5

end ProphetSecretary.Analysis
