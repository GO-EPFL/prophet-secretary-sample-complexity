import ProphetSecretary.Model.ResponseOnSet
import ProphetSecretary.Model.FirstMomentConstants
import ProphetSecretary.Analysis.ExponentialTailThreshold

/-!
# Aggregate mass where the expected tail count is large

The high-tail set in `upmom:logtail` has small Λ-mass. A common measurable
indicator tests all marginal discrepancies simultaneously. The lower selection
estimate and exponential prophet bound are proved prerequisites.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

/-- The high-tail-set bound before division by its positive discrepancy. -/
theorem Instance.highTail_mass_discrepancy (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c a K : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (he : P.firstMomentError δ h w c ≤ firstMomentSurvivalConstant)
    (ha : 2 * h ≤ a) (hK : 0 < K)
    (hKκ : 2 * optimalCompetitiveRatio * Real.exp 1 / firstMomentSelectionConstant δ ≤ K) :
    (firstMomentSelectionConstant δ * a / (2 * (1 + P.totalFirstMoment))) *
      P.aggregatePositiveMeasure.real (Icc a 1 ∩ {x | Real.log (K * (1 + P.totalFirstMoment) / a) ≤ P.tailCount x}) ≤
        P.valueStationarityError δ h w c := by
  classical
  let π := P.valuePolicy (P.integrable_maximum_of_bounded hcap)
    (hδ.le.trans hwδ) (hδ.le.trans hcδ)
  let κ := firstMomentSelectionConstant δ
  let S := P.totalFirstMoment
  let B := Icc a 1 ∩ {x | Real.log (K * (1 + S) / a) ≤ P.tailCount x}
  have ha0 : 0 < a := by linarith
  have hS : 0 ≤ S := P.totalFirstMoment_nonnegative
  have hd : 0 < 1 + S := by linarith
  have hκ : 0 < κ := firstMomentSelectionConstant_positive hδ
  have hB : MeasurableSet B := measurableSet_Icc.inter
    (measurableSet_le measurable_const P.measurable_tailCount)
  have hsub : B ⊆ Ioc (0 : ℝ) 1 := fun x hx => ⟨ha0.trans_le hx.1.1, hx.1.2⟩
  have hf (i : Fin n) (x : ℝ) (hx : x ∈ B) :
      κ * a / (2 * (1 + S)) ≤ π.rule.selectionProbabilityAtValue P π.seedLaw i x -
        optimalCompetitiveRatio * P.prophetProbabilityAtValue π.seedLaw i x := by
    have hsel := P.canonical_selectionAtValue_lower_of_firstMomentError hcap hδ hwδ hcδ hsum hh hquarter
      he i (ha0.trans_le hx.1.1) hx.1.2
    change κ * x / (1 + S) ≤ π.rule.selectionProbabilityAtValue P π.seedLaw i x at hsel
    have hxa := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hx.1.1 hκ.le) hd.le
    have hexp := ProphetSecretary.Analysis.exponential_tail_threshold optimalCompetitiveRatio_nonnegative
      hκ hK hS ha0 hKκ hx.2
    have hprop := mul_le_mul_of_nonneg_left (P.prophetProbabilityAtValue_le_exp_tailCount π.seedLaw i x)
      optimalCompetitiveRatio_nonnegative
    have heq : κ * a / (1 + S) = 2 * (κ * a / (2 * (1 + S))) := by field_simp
    linarith only [hsel, hxa, hexp, hprop, heq]
  have hmass := π.responseDifference_ge_set_mass P hB optimalCompetitiveRatio
    (κ * a / (2 * (1 + S))) hf
  have hm : ∀ (_i : Fin n), Measurable (fun x : ℝ => if x ∈ B then (1 : ℝ) else 0) :=
    fun _ => Measurable.ite hB measurable_const measurable_const
  have hb : ∀ (i : Fin n) x, |if x ∈ B then (1 : ℝ) else 0| ≤ 1 := by
    intro i x
    split_ifs <;> norm_num
  have hs : ∀ (i : Fin n) x, x < 2 * h → (if x ∈ B then (1 : ℝ) else 0) = 0 := by
    intro i x hx
    apply if_neg
    intro hxb
    linarith only [ha, hx, hxb.1.1]
  have hstat := P.valuePerturbation_stationarity hcap hδ hwδ hcδ hsum hh hquarter
    (fun _ x => if x ∈ B then 1 else 0) hm hb hs
  change |π.selectedResponse P (fun _ x => if x ∈ B then 1 else 0) -
      optimalCompetitiveRatio * P.expectedProphetResponse (fun _ x => if x ∈ B then 1 else 0)| ≤
    P.valueStationarityError δ h w c at hstat
  change (κ * a / (2 * (1 + S))) * P.aggregatePositiveMeasure.real B ≤ _
  rw [P.aggregatePositiveMeasure_real_apply_of_subset hB hsub]
  apply hmass.trans
  convert (abs_le.mp hstat).2 using 1
  congr 2 <;> congr 1 <;> funext i x <;> split_ifs <;> rfl

end ProphetSecretary.Model
