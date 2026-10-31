import ProphetSecretary.Model.TerminalScalarValue

/-!
# An actual optimizer for an auxiliary fixed terminal reward

Pull back the zero-rejecting excess-offer optimizer. Every callback acceptance
is strictly above the terminal reward; original identities and zero excess
observations remain in the observed history.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.terminalOptimalPolicy (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) : RandomizedPolicy n :=
  ((P.excessOffers a).positiveValuePolicy (P.excessOffers_integrable_maximum hP ha) hw.le hc).pullbackValuesIndexed (fun _ => excessValueMap a) (fun _ => measurable_excessValueMap a)

lemma Instance.terminalOptimalPolicy_acceptsAbove (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    ∀ r t i x G, (P.terminalOptimalPolicy hP ha hw hc).rule.decide r t i x G = true → a < x := by
  intro r t i x G h
  change decide (0 < excessValueMap a x ∧ (P.excessOffers a).valueThreshold w c
    (unseen (mapHistoryValuesBy (fun _ => excessValueMap a) G)) t i ≤ excessValueMap a x) = true at h
  have hp := (of_decide_eq_true h).1
  have he := positive_excess_reconstructs_value ha hp
  linarith only [hp,he]

lemma Instance.terminalOptimalPolicy_optimal (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a w c : ℝ}
    (ha : 0 ≤ a) (hw : 0 < w) (hc : 0 ≤ c) :
    (P.terminalOptimalPolicy hP ha hw hc).terminalScalarObjective P a w c =
      optimalTerminalScalarValue P a w c := by
  let Q := P.excessOffers a
  have hQ := P.excessOffers_integrable_maximum hP ha
  let π := Q.positiveValuePolicy hQ hw.le hc
  have hpos : ∀ (r : π.Seed) (x u : Fin n → ℝ) (i : Fin n),
      π.rule.ActualSelects r Finset.univ x u i → 0 < x i :=
    fun r x u i hi => Q.positiveValueRule_selects_positive w c r x u i hi
  have he := π.terminalScalarObjective_excessPullback P hP ha hpos w c
  change (P.terminalOptimalPolicy hP ha hw hc).terminalScalarObjective P a w c =
    w*a+π.scalarObjective Q w c at he
  rw [Q.positiveValuePolicy_optimal hQ hw hc] at he
  exact he.trans (optimalTerminalScalarValue_eq_excessValue P hP ha hw hc).symm

end ProphetSecretary.Model
