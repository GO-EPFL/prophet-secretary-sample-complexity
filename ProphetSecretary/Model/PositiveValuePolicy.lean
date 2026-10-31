import ProphetSecretary.Model.BellmanPerformance

/-!
# A zero-rejecting optimal finite scalar policy

Rejecting a zero offer is optimal even when both its reward and continuation
value are zero. This tie choice is useful for fixed-terminal-reward transfers.
Every zero identity remains in subsequent observable history. Optimality is
proved against the full admissible policy class by zero Bellman action loss.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.positiveValueRule (Q : Instance n) (w c : ℝ) : Policy Unit n where
  decide _ t i x H := decide (0 < x ∧ Q.valueThreshold w c (unseen H) t i ≤ x)

lemma Instance.positiveValueRule_isMeasurable (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (Q.positiveValueRule w c).IsMeasurable := by
  apply measurable_to_bool
  let Ω := Unit × (ℝ × (Fin n × (ℝ × History n)))
  change MeasurableSet {q : Ω | decide (0 < q.2.2.2.1 ∧
    Q.valueThreshold w c (unseen q.2.2.2.2) q.2.1 q.2.2.1 ≤ q.2.2.2.1) = true}
  simp only [decide_eq_true_eq]
  have hH : Measurable (fun q : Ω => unseen q.2.2.2.2) := measurable_unseen.comp (by fun_prop)
  have hi : Measurable (fun q : Ω => q.2.2.1) := by fun_prop
  have ht : Measurable (fun q : Ω => q.2.1) := by fun_prop
  have hpair : Measurable (fun q : Ω => (unseen q.2.2.2.2,(q.2.2.1,q.2.1))) :=
    hH.prodMk (hi.prodMk ht)
  have hθ := (Q.valueThreshold_jointMeasurable hQ hw hc).comp hpair
  have hx : Measurable (fun q : Ω => q.2.2.2.1) := by fun_prop
  exact (measurableSet_lt measurable_const hx).inter (measurableSet_le hθ hx)

noncomputable def Instance.positiveValuePolicy (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : RandomizedPolicy n where
  Seed := Unit
  seedLaw := Measure.dirac ()
  rule := Q.positiveValueRule w c
  measurable_rule := Q.positiveValueRule_isMeasurable hQ hw hc

lemma Instance.positiveValueRule_arrivalLoss_zero (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (r : Unit) (x u : Fin n → ℝ) (i : Fin n) :
    (Q.positiveValueRule w c).arrivalBellmanLoss Q w c r x u i = 0 := by
  let θ := Q.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i
  have hV : Q.continuationAtArrival w c x u i = w * θ := Q.continuationAtArrival_eq_threshold hw c x u i
  have hV0 := Q.continuationAtArrival_nonnegative hQ hw.le hc x u i
  unfold Policy.arrivalBellmanLoss Policy.action Instance.positiveValueRule
  simp only [decide_eq_true_eq]
  split_ifs with ha
  · have hbound := mul_le_mul_of_nonneg_left ha.2 hw.le
    have hgood : Q.continuationAtArrival w c x u i ≤ w * x i := hV.le.trans hbound
    rw [max_eq_left hgood,sub_self]
  · have hbad : w * x i ≤ Q.continuationAtArrival w c x u i := by
      by_cases hx : 0 < x i
      · have hθ : x i ≤ θ := le_of_lt (not_le.mp (fun he => ha ⟨hx,he⟩))
        exact (mul_le_mul_of_nonneg_left hθ hw.le).trans_eq hV.symm
      · exact (mul_nonpos_of_nonneg_of_nonpos hw.le (not_lt.mp hx)).trans hV0
    rw [max_eq_right hbad,sub_self]

lemma Instance.positiveValueRule_reachedLoss_zero (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c)
    (r : Unit) (x u : Fin n → ℝ) : (Q.positiveValueRule w c).reachedBellmanLoss Q w c r x u = 0 := by
  unfold Policy.reachedBellmanLoss
  simp only [Q.positiveValueRule_arrivalLoss_zero hQ hw hc, ite_self, Finset.sum_const_zero]

/-- The zero-rejecting policy is an actual optimizer, including c=0 and M=0. -/
theorem Instance.positiveValuePolicy_optimal (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (Q.positiveValuePolicy hQ hw.le hc).scalarObjective Q w c = optimalScalarValue Q w c := by
  let π := Q.positiveValuePolicy hQ hw.le hc
  have h := π.bellman_performanceDifference Q hQ hw hc
  have hz : π.expectedReachedBellmanLoss Q w c = 0 := by
    unfold RandomizedPolicy.expectedReachedBellmanLoss
    apply integral_eq_zero_of_ae
    exact Filter.Eventually.of_forall fun ω => Q.positiveValueRule_reachedLoss_zero hQ hw hc ω.2.2 ω.1 ω.2.1
  rw [hz] at h
  linarith only [h]

lemma Instance.positiveValueRule_selects_positive (Q : Instance n) (w c : ℝ)
    (r : Unit) (x u : Fin n → ℝ) (i : Fin n)
    (hs : (Q.positiveValueRule w c).ActualSelects r Finset.univ x u i) : 0 < x i := by
  have ha := ((Q.positiveValueRule w c).mem_accepted r Finset.univ x u i).mp hs.1.1
  have ha' := ha.2
  change decide (0 < x i ∧ Q.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i ≤ x i) = true at ha'
  exact (of_decide_eq_true ha').1

end ProphetSecretary.Model
