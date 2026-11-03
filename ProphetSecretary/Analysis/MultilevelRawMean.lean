import ProphetSecretary.Analysis.MultilevelPayoffMoments
import Mathlib.Tactic.FieldSimp

/-! # Integrability and telescoping of the raw multilevel mean -/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Analysis

noncomputable def multilevelBaseTerm {State Seed Transition : Type*}
    [MeasurableSpace Seed] (D : MultilevelRecursion State Seed Transition ℝ)
    (r : ℕ) (x : State) (j : Fin (4 ^ (r + 1)))
    (t : MultilevelTree Seed (r + 1)) : ℝ :=
  D.payoff x (D.sample x ((multilevelNodeMeasurableEquiv Seed r t).1 j)) 0

noncomputable def multilevelPairTerm {State Seed Transition : Type*}
    [MeasurableSpace Seed] (D : MultilevelRecursion State Seed Transition ℝ)
    (r : ℕ) (x : State) (l : Fin r) (j : Fin (4 ^ (r - l.val)))
    (t : MultilevelTree Seed (r + 1)) : ℝ :=
  let d := multilevelNodeMeasurableEquiv Seed r t
  multilevelPayoffEstimate D (l.val + 1) x (d.2.1 l j, d.2.2.1 l j) -
    multilevelPayoffEstimate D l.val x (d.2.1 l j, d.2.2.2 l j)

lemma integrable_multilevelSeedBase {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hPay : ∀ x y v, 0 ≤ v → v ≤ 5 → 0 ≤ D.payoff x y v ∧ D.payoff x y v ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (x : State) :
    Integrable (fun s => D.payoff x (D.sample x s) 0) μ := by
  have hs : Measurable (fun s : Seed => D.sample x s) :=
    hD.sample.comp (measurable_const.prodMk measurable_id)
  have hf : Measurable (fun s : Seed => D.payoff x (D.sample x s) 0) :=
    hD.payoff.comp ((measurable_const.prodMk hs).prodMk measurable_const)
  apply Integrable.of_bound hf.aestronglyMeasurable 1
  exact ae_of_all _ (fun s => by
    have hb := hPay x (D.sample x s) 0 le_rfl (by norm_num)
    rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
    exact hb.2)

lemma integrable_multilevelBaseTerm {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hPay : ∀ x y v, 0 ≤ v → v ≤ 5 → 0 ≤ D.payoff x y v ∧ D.payoff x y v ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State)
    (j : Fin (4 ^ (r + 1))) :
    Integrable (multilevelBaseTerm D r x j) (multilevelTreeLaw μ (r + 1)) := by
  exact (multilevelBase_measurePreserving μ r j).integrable_comp_of_integrable
    (integrable_multilevelSeedBase D hD hPay μ x)

lemma integrable_multilevelPairTerm {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y v, 0 ≤ v → v ≤ 5 → 0 ≤ D.payoff x y v ∧ D.payoff x y v ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State)
    (l : Fin r) (j : Fin (4 ^ (r - l.val))) :
    Integrable (multilevelPairTerm D r x l j) (multilevelTreeLaw μ (r + 1)) := by
  have hp := multilevelPair_measurePreserving μ r l j
  have hu : Measurable (fun q : Seed × (MultilevelTree Seed (l.val + 1) × MultilevelTree Seed l.val) =>
      (q.1, q.2.1)) := by fun_prop
  have hl : Measurable (fun q : Seed × (MultilevelTree Seed (l.val + 1) × MultilevelTree Seed l.val) =>
      (q.1, q.2.2)) := by fun_prop
  have hm := ((measurable_multilevelPayoffEstimate D hD (l.val + 1) x).comp
    (hu.comp hp.measurable)).sub
      ((measurable_multilevelPayoffEstimate D hD l.val x).comp (hl.comp hp.measurable))
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact ae_of_all _ (fun t => by
    let d := multilevelNodeMeasurableEquiv Seed r t
    have hb := multilevelPayoffEstimate_bounds D hEmpty hPay (l.val + 1) x
      (d.2.1 l j, d.2.2.1 l j)
    have hc := multilevelPayoffEstimate_bounds D hEmpty hPay l.val x
      (d.2.1 l j, d.2.2.2 l j)
    change ‖multilevelPayoffEstimate D (l.val + 1) x (d.2.1 l j, d.2.2.1 l j) -
      multilevelPayoffEstimate D l.val x (d.2.1 l j, d.2.2.2 l j)‖ ≤ 1
    rw [Real.norm_eq_abs]
    exact abs_le.mpr ⟨by linarith [hb.1, hb.2, hc.1, hc.2],
      by linarith [hb.1, hb.2, hc.1, hc.2]⟩)

private lemma integral_finiteAverage {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (N : ℕ) (hN : 0 < N) (f : Fin N → Ω → ℝ)
    (hf : ∀ j, Integrable (f j) μ) (a : ℝ) (ha : ∀ j, (∫ q, f j q ∂μ) = a) :
    (∫ q, (1 / (N : ℝ)) * ∑ j : Fin N, f j q ∂μ) = a := by
  rw [integral_const_mul, integral_finsetSum Finset.univ (fun j _ => hf j)]
  simp_rw [ha]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hNr : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

/-- The mean of the literal raw estimator telescopes to its last recursive
level. The proof uses the derived product marginals of its actual seed tree. -/
theorem integral_multilevelRawEstimate {State Seed Transition : Type*}
    [MeasurableSpace State] [MeasurableSpace Seed] [MeasurableSpace Transition]
    (D : MultilevelRecursion State Seed Transition ℝ) (hD : D.IsMeasurable)
    (hEmpty : ∀ x, D.isEmpty x = true → 0 ≤ D.emptyValue x ∧ D.emptyValue x ≤ 5)
    (hPay : ∀ x y v, 0 ≤ v → v ≤ 5 → 0 ≤ D.payoff x y v ∧ D.payoff x y v ≤ 1)
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (x : State) :
    (∫ t, multilevelRawEstimate D r x t ∂multilevelTreeLaw μ (r + 1)) =
      D.offset x + D.coefficient x * multilevelExpectedPayoff D μ r x := by
  have hbInt (j : Fin (4 ^ (r + 1))) := integrable_multilevelBaseTerm D hD hPay μ r x j
  have hpInt (l : Fin r) (j : Fin (4 ^ (r - l.val))) :=
    integrable_multilevelPairTerm D hD hEmpty hPay μ r x l j
  have hbaseInt := (integrable_finsetSum Finset.univ (fun j _ => hbInt j)).const_mul
    (1 / ((4 : ℝ) ^ (r + 1)))
  have hlevelInt (l : Fin r) :=
    (integrable_finsetSum Finset.univ (fun j _ => hpInt l j)).const_mul
      (1 / ((4 : ℝ) ^ (r - l.val)))
  have hlevelsInt := integrable_finsetSum Finset.univ (fun l _ => hlevelInt l)
  have hbaseMean :
      (∫ t, (1 / ((4 : ℝ) ^ (r + 1))) *
        ∑ j : Fin (4 ^ (r + 1)), multilevelBaseTerm D r x j t
          ∂multilevelTreeLaw μ (r + 1)) = multilevelExpectedPayoff D μ 0 x := by
    have hb (j : Fin (4 ^ (r + 1))) :
        (∫ t, multilevelBaseTerm D r x j t ∂multilevelTreeLaw μ (r + 1)) =
          multilevelExpectedPayoff D μ 0 x := by
      rw [multilevelExpectedPayoff_zero]
      exact integral_multilevelBase μ r j (fun s => D.payoff x (D.sample x s) 0)
        (integrable_multilevelSeedBase D hD hPay μ x).aestronglyMeasurable
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      integral_finiteAverage (multilevelTreeLaw μ (r + 1)) (4 ^ (r + 1)) (by positivity)
        (multilevelBaseTerm D r x) hbInt (multilevelExpectedPayoff D μ 0 x) hb
  have hlevelMean (l : Fin r) :
      (∫ t, (1 / ((4 : ℝ) ^ (r - l.val))) *
        ∑ j : Fin (4 ^ (r - l.val)), multilevelPairTerm D r x l j t
          ∂multilevelTreeLaw μ (r + 1)) =
        multilevelExpectedPayoff D μ (l.val + 1) x - multilevelExpectedPayoff D μ l.val x := by
    have hp (j : Fin (4 ^ (r - l.val))) :
        (∫ t, multilevelPairTerm D r x l j t ∂multilevelTreeLaw μ (r + 1)) =
          multilevelExpectedPayoff D μ (l.val + 1) x - multilevelExpectedPayoff D μ l.val x :=
      integral_multilevelPair_payoff_sub D hD hEmpty hPay μ r l j x
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      integral_finiteAverage (multilevelTreeLaw μ (r + 1)) (4 ^ (r - l.val)) (by positivity)
        (multilevelPairTerm D r x l) (hpInt l)
        (multilevelExpectedPayoff D μ (l.val + 1) x - multilevelExpectedPayoff D μ l.val x) hp
  have htel : (∑ l : Fin r, (multilevelExpectedPayoff D μ (l.val + 1) x -
      multilevelExpectedPayoff D μ l.val x)) =
        multilevelExpectedPayoff D μ r x - multilevelExpectedPayoff D μ 0 x := by
    simpa only [Finset.sum_range] using
      Finset.sum_range_sub (fun k => multilevelExpectedPayoff D μ k x) r
  change (∫ t, D.offset x + D.coefficient x *
    ((1 / ((4 : ℝ) ^ (r + 1))) *
      ∑ j : Fin (4 ^ (r + 1)), multilevelBaseTerm D r x j t +
      ∑ l : Fin r, (1 / ((4 : ℝ) ^ (r - l.val))) *
        ∑ j : Fin (4 ^ (r - l.val)), multilevelPairTerm D r x l j t)
        ∂multilevelTreeLaw μ (r + 1)) = _
  have htotalInt := (hbaseInt.add hlevelsInt).const_mul (D.coefficient x)
  dsimp only [Pi.add_apply] at htotalInt
  rw [integral_add (integrable_const _) htotalInt,
    integral_const_mul, integral_add hbaseInt hlevelsInt,
    integral_finsetSum Finset.univ (fun l _ => hlevelInt l)]
  simp only [hbaseMean, hlevelMean]
  rw [htel]
  simp only [integral_const, probReal_univ, one_smul]
  ring

end ProphetSecretary.Analysis
