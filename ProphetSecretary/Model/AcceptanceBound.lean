import ProphetSecretary.Model.PositiveSelection

/-!
# Acceptance probability near a small scalar gap

The indicator test from `upmom:stationarity` controls large selections. Waiting
controls small selections through their terminal window. Their sum is the
canonical acceptance probability, since zero selections have probability zero.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma RandomizedPolicy.smallResponse_eq_probability_sum (π : RandomizedPolicy n)
    (P : Instance n) (a : ℝ) :
    π.selectedResponse P (fun _ x => if 0 < x ∧ x < a then 1 else 0) =
      ∑ i, (P.worldLaw π.seedLaw).real {ω : π.World |
        π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i ∧ 0 < ω.1 i ∧ ω.1 i < a} := by
  let E : Fin n → Set π.World := fun i => {ω |
    π.rule.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i ∧ 0 < ω.1 i ∧ ω.1 i < a}
  have hm (i : Fin n) : MeasurableSet (E i) :=
    (π.rule.measurableSet_actualSelects π.measurable_rule (by fun_prop)
      (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i).inter
      ((measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst)).inter
        (measurableSet_lt ((measurable_pi_apply i).comp measurable_fst) measurable_const))
  let f : Fin n → π.World → ℝ := fun i ω => if ω ∈ E i then 1 else 0
  have hI (i : Fin n) : Integrable (f i) (P.worldLaw π.seedLaw) := by
    apply Integrable.of_bound (Measurable.ite (hm i) measurable_const measurable_const).aestronglyMeasurable 1
    exact Eventually.of_forall fun ω => by change ‖if ω ∈ E i then (1 : ℝ) else 0‖ ≤ 1; split_ifs <;> norm_num
  have heq : (fun ω : π.World => π.rule.mappedReward
      (fun _ x => if 0 < x ∧ x < a then 1 else 0) ω.2.2 Finset.univ ω.1 ω.2.1) =
      fun ω => ∑ i, f i ω := by
    funext ω
    unfold Policy.mappedReward
    apply Finset.sum_congr rfl
    intro i _
    dsimp [f, E]
    split_ifs <;> simp_all
  unfold selectedResponse
  rw [heq, integral_finsetSum _ (fun i _ => hI i)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [f, E, Set.indicator_apply, Pi.one_apply] using
    (integral_indicator_one (μ := P.worldLaw π.seedLaw) (hm i))

/-- The acceptance bound used to obtain uniform survival after `upmom:ties`. -/
theorem Instance.canonical_acceptanceResponse_le (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4) :
    let π := P.valuePolicy (P.integrable_maximum_of_bounded hcap)
      (hδ.le.trans hwδ) (hδ.le.trans hcδ)
    π.selectedResponse P (fun _ _ => 1) ≤ optimalCompetitiveRatio +
      (scalarGap P w c / (w * h) + (32 / δ) * (1 + P.positiveCount) ^ 2 * h / w) +
        (2 * w / c) * P.positiveCount * h := by
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  let hP := P.integrable_maximum_of_bounded hcap
  let π := P.valuePolicy hP hw.le hc.le
  let high : Fin n → ℝ → ℝ := fun _ x => if 2 * h ≤ x then 1 else 0
  let low : Fin n → ℝ → ℝ := fun _ x => if 0 < x ∧ x < 2 * h then 1 else 0
  have hmH : ∀ i, Measurable (high i) := fun _ =>
    Measurable.ite (measurableSet_le measurable_const measurable_id) measurable_const measurable_const
  have hmL : ∀ i, Measurable (low i) := fun _ =>
    Measurable.ite ((measurableSet_lt measurable_const measurable_id).inter
      (measurableSet_lt measurable_id measurable_const)) measurable_const measurable_const
  have hbH : ∀ i x, |high i x| ≤ 1 := by intro i x; dsimp [high]; split_ifs <;> norm_num
  have hbL : ∀ i x, |low i x| ≤ 1 := by intro i x; dsimp [low]; split_ifs <;> norm_num
  have heq : (fun i x => high i x + low i x) = (fun (_ : Fin n) x => if 0 < x then (1 : ℝ) else 0) := by
    funext i x
    by_cases hcut : 2 * h ≤ x
    · have hx : 0 < x := lt_of_lt_of_le (by linarith) hcut
      simp [high, low, hcut, hx, not_lt_of_ge hcut]
    · have hlt : x < 2 * h := lt_of_not_ge hcut
      by_cases hx : 0 < x <;> simp [high, low, hcut, hx, hlt]
  have hadd := π.selectedResponse_add P high low hmH hmL hbH hbL
  rw [heq, P.canonical_positiveResponse_eq_oneResponse hP hw hc] at hadd
  have hH := P.canonical_largeSelection_response_le hcap hδ hwδ hcδ hsum hh hquarter
  have hL := P.canonical_smallSelections_sum_le hP hw hc (by positivity : 0 ≤ 2 * h)
  have hl : π.selectedResponse P low ≤ (w * (2 * h) / c) * P.positiveCount := by
    rw [RandomizedPolicy.smallResponse_eq_probability_sum]
    exact hL
  change π.selectedResponse P (fun _ _ => 1) ≤ _
  change π.selectedResponse P high ≤ _ at hH
  have he : (w * (2 * h) / c) * P.positiveCount = (2 * w / c) * P.positiveCount * h := by ring
  rw [he] at hl
  linarith only [hadd, hH, hl]

end ProphetSecretary.Model
