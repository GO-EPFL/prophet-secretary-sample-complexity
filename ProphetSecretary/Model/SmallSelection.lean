import ProphetSecretary.Model.SelectionProphetDistance
import ProphetSecretary.Stability.TerminalWindow

/-!
# Small accepted values arrive in a terminal window

Waiting gives continuation at least c times the remaining horizon. Consequently
a canonical policy can accept a value below a only during the final wa/c units
of time. Independence of the clock and value then bounds the total probability
of such selections by (wa/c)L, as used after `upmom:ties`.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.canonical_smallSelection_window (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c a : ℝ} (hw : 0 < w) (hc : 0 < c)
    (x u : Fin n → ℝ) (i : Fin n)
    (hs : (P.valuePolicy hP hw.le hc.le).rule.ActualSelects () Finset.univ x u i)
    (hsmall : x i < a) : 1 - w * a / c ≤ u i := by
  have hact := ((P.valuePolicy hP hw.le hc.le).rule.mem_accepted () Finset.univ x u i).mp hs.1.1
  have ht : P.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i ≤ x i := by
    simpa only [Policy.action, Instance.valuePolicy, thresholdPolicy, decide_eq_true_eq] using hact.2
  have hwait := P.durationWeight_le_continuationValue hP
    ((unseen (history Finset.univ x u (u i))).erase i)
    (le_max_left 0 (1 - u i)) hw.le hc.le
  have htime := le_max_right 0 (1 - u i)
  unfold Instance.valueThreshold at ht
  have hmul := (div_le_iff₀ hw).mp ht
  have hsmall' := mul_lt_mul_of_pos_left hsmall hw
  have hnum : c * (1 - u i) ≤ w * a := by nlinarith
  rw [mul_comm c] at hnum
  have hd := (le_div_iff₀ hc).mpr hnum
  linarith

lemma Instance.world_lateTail_probability_le {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n)
    {window : ℝ} (hw : 0 ≤ window) (d : ℝ) :
    (P.worldLaw ν).real {ω : World n Seed | 1 - window ≤ ω.2.1 i ∧ d < ω.1 i} ≤
      window * (P.law i (Ioi d)).toReal := by
  by_cases hw1 : window ≤ 1
  · exact le_of_eq (P.world_lateTail_probability ν i hw hw1 d)
  · have hp : MeasurePreserving (fun ω : World n Seed => ω.1 i) (P.worldLaw ν) (P.law i) :=
      (measurePreserving_eval P.law i).comp measurePreserving_fst
    have he := map_measureReal_apply (μ := P.worldLaw ν) hp.measurable (s := Ioi d) measurableSet_Ioi
    rw [hp.map_eq] at he
    have hmono : (P.worldLaw ν).real {ω : World n Seed | 1 - window ≤ ω.2.1 i ∧ d < ω.1 i} ≤
        (P.worldLaw ν).real {ω : World n Seed | d < ω.1 i} :=
      measureReal_mono (fun _ h => h.2)
    have hval : (P.worldLaw ν).real {ω : World n Seed | d < ω.1 i} = (P.law i (Ioi d)).toReal := he.symm
    rw [hval] at hmono
    exact hmono.trans (by nlinarith [ENNReal.toReal_nonneg (a := P.law i (Ioi d))])

/-- This bound remains valid when the formal window exceeds the horizon. -/
theorem Instance.canonical_smallSelection_probability_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c a : ℝ} (hw : 0 < w) (hc : 0 < c)
    (ha : 0 ≤ a) (i : Fin n) :
    (P.worldLaw (Measure.dirac ())).real {ω : World n Unit |
      (P.valuePolicy hP hw.le hc.le).rule.ActualSelects () Finset.univ ω.1 ω.2.1 i ∧
      0 < ω.1 i ∧ ω.1 i < a} ≤ (w * a / c) * (P.law i (Ioi 0)).toReal := by
  have hsub : {ω : World n Unit |
      (P.valuePolicy hP hw.le hc.le).rule.ActualSelects () Finset.univ ω.1 ω.2.1 i ∧
      0 < ω.1 i ∧ ω.1 i < a} ⊆
      {ω : World n Unit | 1 - w * a / c ≤ ω.2.1 i ∧ 0 < ω.1 i} := by
    intro ω hω
    exact ⟨P.canonical_smallSelection_window hP hw hc ω.1 ω.2.1 i hω.1 hω.2.2, hω.2.1⟩
  exact (measureReal_mono hsub).trans
    (P.world_lateTail_probability_le (Measure.dirac ()) i (by positivity) 0)

/-- The sum is controlled by expected positive count, uniformly in instance size. -/
theorem Instance.canonical_smallSelections_sum_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c a : ℝ} (hw : 0 < w) (hc : 0 < c)
    (ha : 0 ≤ a) :
    (∑ i, (P.worldLaw (Measure.dirac ())).real {ω : World n Unit |
      (P.valuePolicy hP hw.le hc.le).rule.ActualSelects () Finset.univ ω.1 ω.2.1 i ∧
      0 < ω.1 i ∧ ω.1 i < a}) ≤ (w * a / c) * P.positiveCount := by
  calc
    _ ≤ ∑ i, (w * a / c) * (P.law i (Ioi 0)).toReal :=
      Finset.sum_le_sum fun i _ => P.canonical_smallSelection_probability_le hP hw hc ha i
    _ = _ := by rw [← Finset.mul_sum]; rfl

lemma Instance.expectedProphetResponse_abs_le_one (P : Instance n)
    (ψ : Fin n → ℝ → ℝ) (hb : ∀ i a, |ψ i a| ≤ 1) :
    |P.expectedProphetResponse ψ| ≤ 1 := by
  have hn := norm_integral_le_of_norm_le_const (μ := P.valuesLaw) (f := prophetResponse ψ)
    (Eventually.of_forall fun x => by
      simpa only [Real.norm_eq_abs] using prophetResponse_abs_le ψ zero_le_one hb x)
  simpa only [Instance.expectedProphetResponse, Real.norm_eq_abs, probReal_univ, mul_one] using hn

/-- The common indicator test in the survival argument following `upmom:ties`. -/
theorem Instance.canonical_largeSelection_response_le (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4) :
    let π := P.valuePolicy (P.integrable_maximum_of_bounded hcap)
      (hδ.le.trans hwδ) (hδ.le.trans hcδ)
    π.selectedResponse P (fun _ x => if 2 * h ≤ x then 1 else 0) ≤
      optimalCompetitiveRatio + scalarGap P w c / (w * h) +
        (32 / δ) * (1 + P.positiveCount) ^ 2 * h / w := by
  let ψ : Fin n → ℝ → ℝ := fun _ x => if 2 * h ≤ x then 1 else 0
  have hm : ∀ i, Measurable (ψ i) := fun _ =>
    Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const
  have hb : ∀ i x, |ψ i x| ≤ 1 := by intro i x; dsimp [ψ]; split_ifs <;> norm_num
  have hs : ∀ i x, x < 2 * h → ψ i x = 0 := by
    intro i x hx
    exact if_neg (not_le.mpr hx)
  have hstat := P.valuePerturbation_stationarity hcap hδ hwδ hcδ hsum hh hquarter ψ hm hb hs
  have hD := (abs_le.mp (P.expectedProphetResponse_abs_le_one ψ hb)).2
  have hCD := mul_le_mul_of_nonneg_left hD optimalCompetitiveRatio_nonnegative
  dsimp only at hstat ⊢
  dsimp only [ψ] at hstat
  rw [mul_one] at hCD
  linarith [le_abs_self ((P.valuePolicy (P.integrable_maximum_of_bounded hcap)
    (hδ.le.trans hwδ) (hδ.le.trans hcδ)).selectedResponse P ψ -
      optimalCompetitiveRatio * P.expectedProphetResponse ψ)]

end ProphetSecretary.Model
