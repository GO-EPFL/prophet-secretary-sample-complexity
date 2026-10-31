import ProphetSecretary.Model.FirstMomentError

/-!
# Responses supported at one value

A common singleton indicator turns the selection response into the sum of the
value-conditioned selection probabilities weighted by marginal atom masses.
For the prophet it is exactly the probability that the maximum equals that
positive value, including ties through the proved deterministic tie-break.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.aggregateAtomMass (P : Instance n) (a : ℝ) : ℝ :=
  ∑ i, (P.law i).real {a}

lemma measurable_singletonTest (a : ℝ) : Measurable (fun x : ℝ => if x = a then (1 : ℝ) else 0) :=
  Measurable.ite (measurableSet_eq_fun measurable_id measurable_const) measurable_const measurable_const

lemma singletonTest_abs_le_one (a x : ℝ) : |if x = a then (1 : ℝ) else 0| ≤ 1 := by
  split_ifs <;> norm_num

lemma RandomizedPolicy.selectedResponse_singleton (π : RandomizedPolicy n) (P : Instance n) (a : ℝ) :
    π.selectedResponse P (fun _ x => if x = a then 1 else 0) =
      ∑ i, (P.law i).real {a} * π.rule.selectionProbabilityAtValue P π.seedLaw i a := by
  rw [π.selectedResponse_eq_marginal_integrals P _ (fun _ => measurable_singletonTest a)
    (fun _ x => singletonTest_abs_le_one a x)]
  apply Finset.sum_congr rfl
  intro i _
  have heq : (fun x => π.rule.selectionProbabilityAtValue P π.seedLaw i x *
      (if x = a then (1 : ℝ) else 0)) =
      ({a} : Set ℝ).indicator (π.rule.selectionProbabilityAtValue P π.seedLaw i) := by
    funext x
    by_cases hx : x = a <;> simp [hx]
  rw [heq, integral_indicator (measurableSet_singleton a), integral_singleton, smul_eq_mul]

lemma prophetResponse_singleton (a : ℝ) (ha : 0 < a) (x : Fin n → ℝ) :
    prophetResponse (fun _ v => if v = a then 1 else 0) x =
      if Instance.maximum x = a then 1 else 0 := by
  by_cases hm : 0 < Instance.maximum x
  · obtain ⟨i, hi⟩ := exists_prophetWins hm
    rw [prophetResponse_eq_of_winner _ hi, hi.2.1]
  · have hz := le_antisymm (not_lt.mp hm) (Instance.maximum_nonnegative x)
    rw [prophetResponse_zero_of_maximum_zero _ hz]
    have hn : Instance.maximum x ≠ a := by rw [hz]; exact ne_of_lt ha
    exact (if_neg hn).symm

lemma Instance.expectedProphetResponse_singleton (P : Instance n) (a : ℝ) (ha : 0 < a) :
    P.expectedProphetResponse (fun _ x => if x = a then 1 else 0) =
      P.valuesLaw.real {x | Instance.maximum x = a} := by
  unfold expectedProphetResponse
  simp_rw [prophetResponse_singleton a ha]
  simpa only [Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
    (integral_indicator_one (μ := P.valuesLaw)
      (measurableSet_eq_fun Instance.measurable_maximum measurable_const))

/-- `upmom:atomeq`, with the source constants and no positive-M assumption. -/
theorem Instance.canonical_aggregateAtom_bound (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {δ h w c : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c) (hsum : w + c = 1)
    (hh : 0 < h) (hquarter : h ≤ 1 / 4)
    (he : P.firstMomentError δ h w c ≤ (1 - optimalCompetitiveRatio) / 2)
    {a : ℝ} (ha : 2 * h ≤ a) (ha1 : a ≤ 1) :
    let ρ := (1 - optimalCompetitiveRatio) / 2
    let γ := min (ρ / 4) (δ / 2)
    ((γ * ρ / 2) * a / (1 + P.totalFirstMoment)) * P.aggregateAtomMass a ≤
      optimalCompetitiveRatio * P.valuesLaw.real {x | Instance.maximum x = a} +
        P.valueStationarityError δ h w c := by
  let π := P.valuePolicy (P.integrable_maximum_of_bounded hcap)
    (hδ.le.trans hwδ) (hδ.le.trans hcδ)
  let ρ := (1 - optimalCompetitiveRatio) / 2
  let γ := min (ρ / 4) (δ / 2)
  let b := (γ * ρ / 2) * a / (1 + P.totalFirstMoment)
  have ha0 : 0 < a := by linarith
  have hs (i : Fin n) : b ≤ π.rule.selectionProbabilityAtValue P π.seedLaw i a :=
    P.canonical_selectionAtValue_lower_of_firstMomentError hcap hδ hwδ hcδ hsum hh hquarter he i ha0 ha1
  have hA : b * P.aggregateAtomMass a ≤ π.selectedResponse P (fun _ x => if x = a then 1 else 0) := by
    rw [π.selectedResponse_singleton P a]
    calc
      _ = ∑ i, (P.law i).real {a} * b := by
        unfold aggregateAtomMass
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hs i) measureReal_nonneg
  have hsupport : ∀ (i : Fin n) (x : ℝ), x < 2 * h → (if x = a then (1 : ℝ) else 0) = 0 := by
    intro i x hx
    apply if_neg
    intro hxa
    rw [hxa] at hx
    linarith only [ha, hx]
  have hstat := P.valuePerturbation_stationarity hcap hδ hwδ hcδ hsum hh hquarter
    (fun _ x => if x = a then 1 else 0) (fun _ => measurable_singletonTest a)
    (fun _ x => singletonTest_abs_le_one a x) hsupport
  change |π.selectedResponse P (fun _ x => if x = a then 1 else 0) -
    optimalCompetitiveRatio * P.expectedProphetResponse (fun _ x => if x = a then 1 else 0)| ≤
      P.valueStationarityError δ h w c at hstat
  rw [P.expectedProphetResponse_singleton a ha0] at hstat
  change b * P.aggregateAtomMass a ≤ _
  linarith only [hA, (abs_le.mp hstat).2]

end ProphetSecretary.Model
