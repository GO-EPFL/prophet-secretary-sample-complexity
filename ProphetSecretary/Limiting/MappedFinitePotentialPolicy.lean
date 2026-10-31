import ProphetSecretary.Limiting.FinitePotentialPolicy
import ProphetSecretary.Model.PositiveMappedValuePolicy
import ProphetSecretary.Model.ExcessValueMap

/-!
# A shared zero-rejecting potential rule on excess current values

The callbacks use original retained histories only through their unseen
identities and map only the current value. They ignore anonymous past except
for elapsed time and are independent of the realized anonymous count. Their
finite adapters have exactly zero mapped Bellman loss.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

noncomputable def mappedPositivePotentialRule (Q : Model.Instance n) (a w c : ℝ) : HybridRule n Unit where
  individual _ t i x H _ := decide (0 < Model.excessValueMap a x ∧ Q.valueThreshold w c (Model.unseen H) t i ≤ Model.excessValueMap a x)
  poisson _ t x H _ := decide (0 < Model.excessValueMap a x ∧ poissonThreshold Q w c (Model.unseen H) t ≤ Model.excessValueMap a x)

lemma mappedPositivePotentialRule_isMeasurable (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (a : ℝ) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (mappedPositivePotentialRule Q a w c).IsMeasurable := by
  constructor
  · let Ω := Unit × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point))))
    have hp : Measurable (fun q : Ω => (q.1,(q.2.1,(q.2.2.1,(q.2.2.2.1,q.2.2.2.2.1))))) := by fun_prop
    exact (Q.positiveMappedValueRule_isMeasurable hQ (fun _ => Model.excessValueMap a)
      (fun _ => Model.measurable_excessValueMap a) hw hc).comp hp
  · apply measurable_to_bool
    let Ω := Unit × (Point × (Model.History n × Measure Point))
    change MeasurableSet {q : Ω | decide (0 < Model.excessValueMap a q.2.1.2 ∧
      poissonThreshold Q w c (Model.unseen q.2.2.1) q.2.1.1 ≤ Model.excessValueMap a q.2.1.2) = true}
    simp only [decide_eq_true_eq]
    have ht : Measurable (fun q : Ω => q.2.1.1) := by fun_prop
    have hx : Measurable (fun q : Ω => Model.excessValueMap a q.2.1.2) :=
      (Model.measurable_excessValueMap a).comp (by fun_prop)
    have hH : Measurable (fun q : Ω => Model.unseen q.2.2.1) := Model.measurable_unseen.comp (by fun_prop)
    have hθ := (measurable_poissonThreshold Q hQ hw hc).comp (hH.prodMk ht)
    exact (measurableSet_lt measurable_const hx).inter (measurableSet_le hθ hx)

noncomputable def mappedPositivePotentialPolicy (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (a : ℝ) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    RandomizedHybridPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := mappedPositivePotentialRule Q a w c
  measurable_rule := mappedPositivePotentialRule_isMeasurable Q hQ a hw hc

lemma mappedPositivePotentialRule_adapter (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (a : ℝ) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (N : ℕ) :
    (mappedPositivePotentialRule Q a w c).asFinitePolicy N =
      (Q.appendZeros N).positiveMappedValueRule (fun _ => Model.excessValueMap a) w c := by
  change Model.Policy.mk _ = Model.Policy.mk _
  congr 1
  funext r t i x H
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.addCases_left,mappedPositivePotentialRule]
    simp only [appended_valueThreshold_individual Q hQ hw hc,retainedSet_unseen]
  | right j =>
    simp only [Fin.addCases_right,mappedPositivePotentialRule]
    simp only [appended_valueThreshold_poisson Q hQ hw hc,retainedSet_unseen]

lemma mappedPositivePotentialRule_branch_loss_zero (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (a : ℝ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (N : ℕ) (r : Unit) (x u : Fin (n + N) → ℝ) :
    ((mappedPositivePotentialRule Q a w c).asFinitePolicy N).mappedReachedLoss (Q.appendZeros N)
      (fun _ => Model.excessValueMap a) w c r x u = 0 := by
  rw [mappedPositivePotentialRule_adapter Q hQ a hw.le hc N]
  exact (Q.appendZeros N).positiveMappedValueRule_reachedLoss_zero
    (Q.appendZeros_integrable_maximum N hQ) (fun _ => Model.excessValueMap a) hw hc r x u

end ProphetSecretary.Limiting
