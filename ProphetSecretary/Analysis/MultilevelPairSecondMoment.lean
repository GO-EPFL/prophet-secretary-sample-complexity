import ProphetSecretary.Analysis.MultilevelPairError
import Mathlib.Probability.HasLaw

/-! # Second moments of the actual adjacent-level differences -/

open MeasureTheory

namespace ProphetSecretary.Analysis

/-- Shared transitions turn adjacent uniform squared-error bounds into the
paired-difference second moment used by `alg:mlmc-mse`. -/
theorem integral_multilevelPairTerm_sq_le {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y w, 0 ≤ w → w ≤ 5 → 0 ≤ D.payoff x y w ∧ D.payoff x y w ≤ 1)
    (hLip : ∀ x y, LipschitzWith 1 (D.payoff x y))
    (v : State → ℝ) (hv : Measurable v) (hvb : ∀ x, 0 ≤ v x ∧ v x ≤ 5)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (l : Fin r)
    (Eu El : ℝ)
    (hEu : ∀ y, (∫ t, (multilevelEstimate D (l.val + 1) y t - v y) ^ 2
      ∂multilevelTreeLaw μ (l.val + 1)) ≤ Eu)
    (hEl : ∀ y, (∫ t, (multilevelEstimate D l.val y t - v y) ^ 2
      ∂multilevelTreeLaw μ l.val) ≤ El)
    (x : State) (j : Fin (4 ^ (r - l.val))) :
    (∫ t, (multilevelPairTerm D r x l j t) ^ 2 ∂multilevelTreeLaw μ (r + 1)) ≤
      2 * (Eu + El) := by
  have hp := multilevelPair_measurePreserving μ r l j
  have hu : MeasurePreserving
      (fun q : Seed × (MultilevelTree Seed (l.val + 1) × MultilevelTree Seed l.val) => (q.1, q.2.1))
      (μ.prod ((multilevelTreeLaw μ (l.val + 1)).prod (multilevelTreeLaw μ l.val)))
      (μ.prod (multilevelTreeLaw μ (l.val + 1))) :=
    (MeasurePreserving.id μ).prod measurePreserving_fst
  have hl : MeasurePreserving
      (fun q : Seed × (MultilevelTree Seed (l.val + 1) × MultilevelTree Seed l.val) => (q.1, q.2.2))
      (μ.prod ((multilevelTreeLaw μ (l.val + 1)).prod (multilevelTreeLaw μ l.val)))
      (μ.prod (multilevelTreeLaw μ l.val)) :=
    (MeasurePreserving.id μ).prod measurePreserving_snd
  have htu := hu.comp hp
  have htl := hl.comp hp
  have hiu := integrable_multilevelChildSqError D hD hEmpty v hv hvb μ (l.val + 1) x
  have hil := integrable_multilevelChildSqError D hD hEmpty v hv hvb μ l.val x
  have huInt := htu.integrable_comp_of_integrable hiu
  have hlInt := htl.integrable_comp_of_integrable hil
  have huEq := htu.hasLaw.integral_comp hiu.aestronglyMeasurable
  have hlEq := htl.hasLaw.integral_comp hil.aestronglyMeasurable
  dsimp only [Function.comp_def] at huInt hlInt huEq hlEq
  let U : MultilevelTree Seed (r + 1) → ℝ := fun t =>
    let d := multilevelNodeMeasurableEquiv Seed r t
    multilevelChildSqError D v (l.val + 1) x (d.2.1 l j, d.2.2.1 l j)
  let L : MultilevelTree Seed (r + 1) → ℝ := fun t =>
    let d := multilevelNodeMeasurableEquiv Seed r t
    multilevelChildSqError D v l.val x (d.2.1 l j, d.2.2.2 l j)
  have hU : Integrable U (multilevelTreeLaw μ (r + 1)) := huInt
  have hL : Integrable L (multilevelTreeLaw μ (r + 1)) := hlInt
  have hpoint (t : MultilevelTree Seed (r + 1)) :
      (multilevelPairTerm D r x l j t) ^ 2 ≤ 2 * (U t + L t) :=
    multilevelPairTerm_sq_le D hLip v r x l j t
  have hiR : Integrable (fun t => 2 * (U t + L t)) (multilevelTreeLaw μ (r + 1)) :=
    (hU.add hL).const_mul 2
  have hiP : Integrable (fun t => (multilevelPairTerm D r x l j t) ^ 2)
      (multilevelTreeLaw μ (r + 1)) := by
    apply hiR.mono_nonneg
      ((integrable_multilevelPairTerm D hD hEmpty hPay μ r x l j).aestronglyMeasurable.pow 2)
    · exact ae_of_all _ (fun _ => sq_nonneg _)
    · exact ae_of_all _ hpoint
  have hUb : (∫ t, U t ∂multilevelTreeLaw μ (r + 1)) ≤ Eu :=
    huEq.le.trans (integral_multilevelChildSqError_le D hD hEmpty v hv hvb μ (l.val + 1) Eu hEu x)
  have hLb : (∫ t, L t ∂multilevelTreeLaw μ (r + 1)) ≤ El :=
    hlEq.le.trans (integral_multilevelChildSqError_le D hD hEmpty v hv hvb μ l.val El hEl x)
  calc
    _ ≤ ∫ t, 2 * (U t + L t) ∂multilevelTreeLaw μ (r + 1) := integral_mono hiP hiR hpoint
    _ = 2 * ((∫ t, U t ∂multilevelTreeLaw μ (r + 1)) +
        ∫ t, L t ∂multilevelTreeLaw μ (r + 1)) := by
      rw [integral_const_mul, integral_add hU hL]
    _ ≤ _ := by linarith

end ProphetSecretary.Analysis
