import ProphetSecretary.Model.BellmanResidualBasic
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.Layercake

/-!
# Bounded positive premia as integrals of offer tails

A nonnegative continuation value makes the positive-part payoff vanish at zero.
For bounded offers its expectation is the integral of strict offer tails above
the continuation threshold. The proof uses actual finite product integration,
including the measurable and integrable indicator kernel.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

noncomputable def premiumTailIndicator (q : ℝ) (z : ℝ × ℝ) : ℝ :=
  if q < z.1 ∧ z.1 < z.2 then 1 else 0

lemma measurable_premiumTailIndicator (q : ℝ) : Measurable (premiumTailIndicator q) :=
  Measurable.ite ((measurableSet_lt measurable_const measurable_fst).inter
    (measurableSet_lt measurable_fst measurable_snd)) measurable_const measurable_const

lemma integral_premiumTailIndicator_level {q a H : ℝ} (hq : 0 ≤ q) (ha : a ≤ H) :
    (∫ x, premiumTailIndicator q (x,a) ∂volume.restrict (Icc 0 H)) = max (a - q) 0 := by
  let E : Set ℝ := {x | q < x ∧ x < a}
  have hE : MeasurableSet E := measurableSet_Ioo
  have hset : E ∩ Icc 0 H = Ioo q a := by
    ext x
    constructor
    · exact fun h => h.1
    · intro hx
      exact ⟨hx, hq.trans hx.1.le, hx.2.le.trans ha⟩
  have h := integral_indicator_one (μ := volume.restrict (Icc 0 H)) hE
  change (∫ x, (if x ∈ E then (1 : ℝ) else 0) ∂volume.restrict (Icc 0 H)) = _
  have heq : (∫ x, (if x ∈ E then (1 : ℝ) else 0) ∂volume.restrict (Icc 0 H)) =
      ((volume.restrict (Icc 0 H)) E).toReal := by
    simpa only [Set.indicator_apply, Pi.one_apply, Measure.real] using h
  rw [heq, Measure.restrict_apply hE, hset, Real.volume_Ioo]
  by_cases hqa : q ≤ a
  · rw [ENNReal.toReal_ofReal (sub_nonneg.mpr hqa), max_eq_left (sub_nonneg.mpr hqa)]
  · rw [ENNReal.ofReal_of_nonpos (sub_nonpos.mpr (not_le.mp hqa).le), ENNReal.toReal_zero,
      max_eq_right (sub_nonpos.mpr (not_le.mp hqa).le)]

lemma integral_premiumTailIndicator_offer (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (q x : ℝ) :
    (∫ a, premiumTailIndicator q (x,a) ∂κ) = if q < x then κ.real (Ioi x) else 0 := by
  by_cases hx : q < x
  · have heq : (fun a => premiumTailIndicator q (x,a)) =
        (Ioi x).indicator (fun _ => (1 : ℝ)) := by
      funext a
      simp only [premiumTailIndicator, hx, true_and, Set.indicator_apply, Set.mem_Ioi]
    rw [heq, if_pos hx]
    change (∫ a, if a ∈ Ioi x then (1 : ℝ) else 0 ∂κ) = _
    simpa only [Set.indicator_apply, Pi.one_apply] using (integral_indicator_one (μ := κ) measurableSet_Ioi)
  · simp only [premiumTailIndicator, hx, false_and, if_false, integral_zero]

lemma positivePart_eq_scaled_threshold (w v a : ℝ) (hw : 0 < w) :
    max (w * a - v) 0 = w * max (a - v / w) 0 := by
  have hv : w * (v / w) = v := by field_simp
  by_cases h : v / w ≤ a
  · have hwa : 0 ≤ w * a - v := by nlinarith only [h, hv, hw]
    rw [max_eq_left hwa, max_eq_left (sub_nonneg.mpr h)]
    nlinarith only [hv]
  · have hwa : w * a - v ≤ 0 := by nlinarith only [h, hv, hw]
    rw [max_eq_right hwa, max_eq_right (sub_nonpos.mpr (not_le.mp h).le), mul_zero]

/-- Layer-cake representation of the bounded positive premium. Strict tails
permit arbitrary atoms in the offer law. -/
theorem positivePremium_eq_integral_tail (κ : Measure ℝ) [IsProbabilityMeasure κ]
    {H w v : ℝ} (hcap : ∀ᵐ a ∂κ, a ≤ H) (hw : 0 < w) (hv : 0 ≤ v) :
    positivePremium κ w v = w * ∫ x in Icc 0 H,
      (if v / w < x then κ.real (Ioi x) else 0) := by
  let q := v / w
  let ν := volume.restrict (Icc (0 : ℝ) H)
  let F : ℝ × ℝ → ℝ := premiumTailIndicator q
  have hI : Integrable F (ν.prod κ) := by
    apply Integrable.of_bound (measurable_premiumTailIndicator q).aestronglyMeasurable 1
    exact Eventually.of_forall fun z => by
      change ‖if _ then (1 : ℝ) else 0‖ ≤ 1
      split_ifs <;> norm_num
  have hswap := integral_prod_symm F hI
  have hpoint : (fun a => max (w * a - v) 0) =ᵐ[κ]
      (fun a => w * ∫ x, F (x,a) ∂ν) := by
    filter_upwards [hcap] with a ha
    rw [positivePart_eq_scaled_threshold w v a hw]
    rw [integral_premiumTailIndicator_level (div_nonneg hv hw.le) ha]
  unfold positivePremium
  rw [integral_congr_ae hpoint, integral_const_mul]
  congr 1
  rw [← hswap, integral_prod F hI]
  apply integral_congr_ae
  exact Eventually.of_forall fun x => integral_premiumTailIndicator_offer κ q x

end ProphetSecretary.Model
