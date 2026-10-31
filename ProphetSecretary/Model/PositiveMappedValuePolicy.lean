import ProphetSecretary.Model.PositiveValuePolicy
import ProphetSecretary.Model.MappedRewardPerformance

/-!
# A zero-rejecting finite potential applied to mapped current values

The policy compares only the mapped current value with its design threshold.
It keeps the original history and uses its unseen identities. Its mapped
Bellman loss vanishes pointwise; no inverse observation map is required.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def Instance.positiveMappedValueRule (Q : Instance n) (f : Fin n → ℝ → ℝ) (w c : ℝ) : Policy Unit n where
  decide _ t i x H := decide (0 < f i x ∧ Q.valueThreshold w c (unseen H) t i ≤ f i x)

lemma Instance.positiveMappedValueRule_isMeasurable (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (f : Fin n → ℝ → ℝ) (hf : ∀ i, Measurable (f i))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : (Q.positiveMappedValueRule f w c).IsMeasurable := by
  apply measurable_to_bool
  let Ω := Unit × (ℝ × (Fin n × (ℝ × History n)))
  change MeasurableSet {q : Ω | decide (0 < f q.2.2.1 q.2.2.2.1 ∧
    Q.valueThreshold w c (unseen q.2.2.2.2) q.2.1 q.2.2.1 ≤ f q.2.2.1 q.2.2.2.1) = true}
  simp only [decide_eq_true_eq]
  have hH : Measurable (fun q : Ω => unseen q.2.2.2.2) := measurable_unseen.comp (by fun_prop)
  have hi : Measurable (fun q : Ω => q.2.2.1) := by fun_prop
  have ht : Measurable (fun q : Ω => q.2.1) := by fun_prop
  have hx : Measurable (fun q : Ω => q.2.2.2.1) := by fun_prop
  have hF : Measurable (fun z : Fin n × ℝ => f z.1 z.2) := by
    apply measurable_from_prod_countable_right
    intro i
    exact hf i
  have hFx := hF.comp (hi.prodMk hx)
  have hθ := (Q.valueThreshold_jointMeasurable hQ hw hc).comp (hH.prodMk (hi.prodMk ht))
  exact (measurableSet_lt measurable_const hFx).inter (measurableSet_le hθ hFx)

lemma Instance.positiveMappedValueRule_arrivalLoss_zero (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (f : Fin n → ℝ → ℝ)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (r : Unit) (x u : Fin n → ℝ) (i : Fin n) :
    (Q.positiveMappedValueRule f w c).mappedArrivalLoss Q f w c r x u i = 0 := by
  let θ := Q.valueThreshold w c (unseen (history Finset.univ x u (u i))) (u i) i
  have hV : Q.continuationAtArrival w c x u i = w * θ := Q.continuationAtArrival_eq_threshold hw c x u i
  have hV0 := Q.continuationAtArrival_nonnegative hQ hw.le hc x u i
  unfold Policy.mappedArrivalLoss Policy.action Instance.positiveMappedValueRule
  simp only [decide_eq_true_eq]
  split_ifs with ha
  · have hb := mul_le_mul_of_nonneg_left ha.2 hw.le
    rw [max_eq_left (hV.le.trans hb),sub_self]
  · have hb : w * f i (x i) ≤ Q.continuationAtArrival w c x u i := by
      by_cases hx : 0 < f i (x i)
      · have hθ : f i (x i) ≤ θ := le_of_lt (not_le.mp (fun he => ha ⟨hx,he⟩))
        exact (mul_le_mul_of_nonneg_left hθ hw.le).trans_eq hV.symm
      · exact (mul_nonpos_of_nonneg_of_nonpos hw.le (not_lt.mp hx)).trans hV0
    rw [max_eq_right hb,sub_self]

lemma Instance.positiveMappedValueRule_reachedLoss_zero (Q : Instance n)
    (hQ : Integrable Instance.maximum Q.valuesLaw) (f : Fin n → ℝ → ℝ)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) (r : Unit) (x u : Fin n → ℝ) :
    (Q.positiveMappedValueRule f w c).mappedReachedLoss Q f w c r x u = 0 := by
  unfold Policy.mappedReachedLoss
  simp only [Q.positiveMappedValueRule_arrivalLoss_zero hQ f hw hc,ite_self,Finset.sum_const_zero]

end ProphetSecretary.Model
