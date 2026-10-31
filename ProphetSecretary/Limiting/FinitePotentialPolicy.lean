import ProphetSecretary.Limiting.HybridScalarObjectives
import ProphetSecretary.Model.ZeroAppendContinuation

/-!
# Count-independent rules from a finite continuation potential

A finite design instance determines thresholds for retained individual offers and
for anonymous arrivals. On each analytical finite-array branch the rule agrees
with the finite design policy after appending deterministic-zero marginals.
Thus the same implementation works for every Poisson count without observing it.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n N : ℕ}

noncomputable def poissonThreshold (Q : Model.Instance n) (w c : ℝ)
    (A : Finset (Fin n)) (t : ℝ) : ℝ :=
  Q.continuationValue A (max 0 (1 - t)) w c / w

lemma poissonThreshold_continuous (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (A : Finset (Fin n)) : Continuous (poissonThreshold Q w c A) := by
  have hV := Model.optimalScalarValue_durationWeight_continuousOn (Q.restrictTo A)
    (Q.restrictTo_integrable_maximum A hQ) hw
  have ht : Continuous (fun t : ℝ => c * max 0 (1 - t)) :=
    continuous_const.mul (continuous_const.max (continuous_const.sub continuous_id))
  exact (hV.comp_continuous ht (fun _ => mul_nonneg hc (le_max_left _ _))).div_const w

lemma measurable_poissonThreshold (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (fun z : Finset (Fin n) × ℝ => poissonThreshold Q w c z.1 z.2) := by
  apply measurable_from_prod_countable_right
  intro A
  exact (poissonThreshold_continuous Q hQ hw hc A).measurable

noncomputable def finitePotentialRule (Q : Model.Instance n) (w c : ℝ) : HybridRule n Unit where
  individual _ t i x H _ := decide (Q.valueThreshold w c (Model.unseen H) t i ≤ x)
  poisson _ t x H _ := decide (poissonThreshold Q w c (Model.unseen H) t ≤ x)

lemma finitePotentialRule_isMeasurable (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    (finitePotentialRule Q w c).IsMeasurable := by
  constructor
  · let Ω := Unit × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point))))
    have hH : Measurable (fun z : Ω => Model.unseen z.2.2.2.2.1) :=
      Model.measurable_unseen.comp (by fun_prop)
    have ht : Measurable (fun z : Ω => z.2.1) := by fun_prop
    have hi : Measurable (fun z : Ω => z.2.2.1) := by fun_prop
    have hx : Measurable (fun z : Ω => z.2.2.2.1) := by fun_prop
    have hs := measurableSet_le ((Q.valueThreshold_jointMeasurable hQ hw hc).comp (hH.prodMk (hi.prodMk ht))) hx
    change Measurable (fun z : Ω => decide (Q.valueThreshold w c (Model.unseen z.2.2.2.2.1) z.2.1 z.2.2.1 ≤ z.2.2.2.1))
    have hIf : Measurable (fun z : Ω => if Q.valueThreshold w c (Model.unseen z.2.2.2.2.1) z.2.1 z.2.2.1 ≤ z.2.2.2.1
        then true else false) := Measurable.ite hs measurable_const measurable_const
    convert hIf using 1
    funext z
    split_ifs <;> simp_all
  · let Ω := Unit × (Point × (Model.History n × Measure Point))
    have hH : Measurable (fun z : Ω => Model.unseen z.2.2.1) :=
      Model.measurable_unseen.comp (measurable_fst.comp (measurable_snd.comp measurable_snd))
    have ht : Measurable (fun z : Ω => z.2.1.1) := measurable_fst.comp (measurable_fst.comp measurable_snd)
    have hx : Measurable (fun z : Ω => z.2.1.2) := measurable_snd.comp (measurable_fst.comp measurable_snd)
    have hs := measurableSet_le ((measurable_poissonThreshold Q hQ hw hc).comp (hH.prodMk ht)) hx
    change Measurable (fun z : Ω => decide (poissonThreshold Q w c (Model.unseen z.2.2.1) z.2.1.1 ≤ z.2.1.2))
    have hIf : Measurable (fun z : Ω => if poissonThreshold Q w c (Model.unseen z.2.2.1) z.2.1.1 ≤ z.2.1.2
        then true else false) := Measurable.ite hs measurable_const measurable_const
    convert hIf using 1
    funext z
    split_ifs <;> simp_all

lemma retainedSet_unseen (H : Model.History (n + N)) :
    Model.retainedSet N (Model.unseen H) = Model.unseen (retainedHistory H) := by
  ext i
  simp [Model.retainedSet, Model.unseen, retainedHistory]

lemma retainedSet_erase_individual (A : Finset (Fin (n + N))) (i : Fin n) :
    Model.retainedSet N (A.erase (i.castAdd N)) = (Model.retainedSet N A).erase i := by
  ext j
  simp [Model.retainedSet]

lemma retainedSet_erase_poisson (A : Finset (Fin (n + N))) (j : Fin N) :
    Model.retainedSet N (A.erase (j.natAdd n)) = Model.retainedSet N A := by
  ext i
  have hne : Fin.castAdd N i ≠ Fin.natAdd n j := by
    intro hij
    have hv := congrArg Fin.val hij
    simp only [Fin.val_castAdd, Fin.val_natAdd] at hv
    omega
  simp [Model.retainedSet, hne]

lemma appended_valueThreshold_individual (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (A : Finset (Fin (n + N))) (t : ℝ) (i : Fin n) :
    (Q.appendZeros N).valueThreshold w c A t (i.castAdd N) = Q.valueThreshold w c (Model.retainedSet N A) t i := by
  unfold Model.Instance.valueThreshold Model.Instance.continuationValue
  rw [Q.optimalScalarValue_appendZeros_restrictTo N _ hQ hw (mul_nonneg hc (le_max_left _ _)),
    retainedSet_erase_individual]

lemma appended_valueThreshold_poisson (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (A : Finset (Fin (n + N))) (t : ℝ) (j : Fin N) :
    (Q.appendZeros N).valueThreshold w c A t (j.natAdd n) = poissonThreshold Q w c (Model.retainedSet N A) t := by
  unfold Model.Instance.valueThreshold poissonThreshold Model.Instance.continuationValue
  rw [Q.optimalScalarValue_appendZeros_restrictTo N _ hQ hw (mul_nonneg hc (le_max_left _ _)),
    retainedSet_erase_poisson]

lemma finitePotentialRule_adapter (Q : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (N : ℕ) :
    (finitePotentialRule Q w c).asFinitePolicy N =
      Model.thresholdPolicy (fun (_ : Unit) A t i => (Q.appendZeros N).valueThreshold w c A t i) := by
  change Model.Policy.mk _ = Model.Policy.mk _
  congr 1
  funext r t i x H
  induction i using Fin.addCases with
  | left i =>
    simp only [Fin.addCases_left, finitePotentialRule]
    simp only [appended_valueThreshold_individual Q hQ hw hc, retainedSet_unseen]
  | right j =>
    simp only [Fin.addCases_right, finitePotentialRule]
    simp only [appended_valueThreshold_poisson Q hQ hw hc, retainedSet_unseen]

end ProphetSecretary.Limiting
