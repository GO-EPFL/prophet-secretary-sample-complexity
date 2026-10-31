import ProphetSecretary.Limiting.HybridHorizonContinuity
import ProphetSecretary.Limiting.HybridHorizonSecant
import ProphetSecretary.Limiting.HybridMarkovThreshold
import ProphetSecretary.Model.Restriction

/-!
# Hybrid thresholds from actual continuation values

The continuation supremum still ranges over every admissible hybrid policy.
A retained arrival removes its own identity from the continuation state;
an anonymous arrival leaves the retained unseen set unchanged. The callback
reads identities and elapsed time, including identities revealed by zero
arrivals. These definitions and measurability do not assert optimality of the
constructed threshold rule; that requires a separate verification proof.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def FiniteIntensityHybridInstance.restrictIndividuals (B : FiniteIntensityHybridInstance n)
    (A : Finset (Fin n)) : FiniteIntensityHybridInstance A.card where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals := B.individuals.restrictTo A
  individual_bounded i := B.individual_bounded (Model.stateEmbedding A i)
  intensity := B.intensity
  intensity_supported := B.intensity_supported

noncomputable def remainingTime (t : ℝ) : ℝ≥0 := Real.toNNReal (1-t)

lemma continuous_remainingTime : Continuous remainingTime :=
  continuous_real_toNNReal.comp (continuous_const.sub continuous_id)

lemma coe_remainingTime {t : ℝ} (ht : t ≤ 1) : (remainingTime t : ℝ) = 1-t := by
  simp only [remainingTime,Real.toNNReal_of_nonneg (sub_nonneg.mpr ht)]
  rfl

lemma remainingTime_le_one {t : ℝ} (ht : 0 ≤ t) : remainingTime t ≤ 1 := by
  change Real.toNNReal (1-t) ≤ 1
  have h : Real.toNNReal (1-t) ≤ Real.toNNReal (1 : ℝ) :=
    Real.toNNReal_le_toNNReal (show 1-t ≤ (1 : ℝ) by linarith)
  simpa only [Real.toNNReal_one] using h

noncomputable def FiniteIntensityHybridInstance.valueHybridThreshold (B : FiniteIntensityHybridInstance n)
    (w c : ℝ) (_r : Unit) (A : Finset (Fin n)) (t : ℝ) (candidate : Option (Fin n)) : ℝ :=
  (B.restrictIndividuals (candidate.elim A (fun i => A.erase i))).continuationValue w c (remainingTime t)/w

noncomputable def FiniteIntensityHybridInstance.valueRule (B : FiniteIntensityHybridInstance n) (w c : ℝ) : HybridRule n Unit :=
  hybridThresholdRule (B.valueHybridThreshold w c)

lemma FiniteIntensityHybridInstance.valueHybridThreshold_continuous (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (A : Finset (Fin n)) (i : Option (Fin n)) :
    Continuous (fun t => B.valueHybridThreshold w c () A t i) :=
  (((B.restrictIndividuals (i.elim A (fun j => A.erase j))).continuous_continuationValue hw hc).comp
    continuous_remainingTime).div_const w

lemma FiniteIntensityHybridInstance.valueHybridThreshold_jointMeasurable (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (fun z : Finset (Fin n) × (Option (Fin n) × ℝ) => B.valueHybridThreshold w c () z.1 z.2.2 z.2.1) := by
  apply measurable_from_prod_countable_right
  intro A
  apply measurable_from_prod_countable_right
  intro i
  exact (B.valueHybridThreshold_continuous hw hc A i).measurable

lemma FiniteIntensityHybridInstance.valueRule_isMeasurable (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : (B.valueRule w c).IsMeasurable := by
  constructor
  · let Ω := Unit × (ℝ × (Fin n × (ℝ × (Model.History n × Measure Point))))
    have hH : Measurable (fun z : Ω => Model.unseen z.2.2.2.2.1) := Model.measurable_unseen.comp (by fun_prop)
    have ht : Measurable (fun z : Ω => z.2.1) := by fun_prop
    have hi : Measurable (fun z : Ω => some z.2.2.1) := by fun_prop
    have hx : Measurable (fun z : Ω => z.2.2.2.1) := by fun_prop
    have hs := measurableSet_le ((B.valueHybridThreshold_jointMeasurable hw hc).comp (hH.prodMk (hi.prodMk ht))) hx
    change Measurable (fun z : Ω => decide (B.valueHybridThreshold w c () (Model.unseen z.2.2.2.2.1) z.2.1 (some z.2.2.1) ≤ z.2.2.2.1))
    have hIf : Measurable (fun z : Ω => if B.valueHybridThreshold w c () (Model.unseen z.2.2.2.2.1) z.2.1 (some z.2.2.1) ≤ z.2.2.2.1 then true else false) :=
      Measurable.ite hs measurable_const measurable_const
    convert hIf using 1
    funext z
    split_ifs <;> simp_all
  · let Ω := Unit × (Point × (Model.History n × Measure Point))
    have hH : Measurable (fun z : Ω => Model.unseen z.2.2.1) := Model.measurable_unseen.comp (by fun_prop)
    have ht : Measurable (fun z : Ω => z.2.1.1) := by fun_prop
    have hx : Measurable (fun z : Ω => z.2.1.2) := by fun_prop
    have hs := measurableSet_le ((B.valueHybridThreshold_jointMeasurable hw hc).comp
      (hH.prodMk ((measurable_const : Measurable (fun _ : Ω => (none : Option (Fin n)))).prodMk ht))) hx
    change Measurable (fun z : Ω => decide (B.valueHybridThreshold w c () (Model.unseen z.2.2.1) z.2.1.1 none ≤ z.2.1.2))
    have hIf : Measurable (fun z : Ω => if B.valueHybridThreshold w c () (Model.unseen z.2.2.1) z.2.1.1 none ≤ z.2.1.2 then true else false) :=
      Measurable.ite hs measurable_const measurable_const
    convert hIf using 1
    funext z
    split_ifs <;> simp_all

lemma FiniteIntensityHybridInstance.valueHybridThreshold_pos (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) (A : Finset (Fin n)) (i : Option (Fin n))
    {t : ℝ} (ht : t < 1) : 0 < B.valueHybridThreshold w c () A t i := by
  let C := B.restrictIndividuals (i.elim A (fun j => A.erase j))
  have hu : 0 < (remainingTime t : ℝ) := by rw [coe_remainingTime ht.le]; linarith
  have hV := (C.remainingHorizon (remainingTime t)).durationReward_le_optimalScalarValue (w := w)
    (c := c*(remainingTime t : ℝ)) hw.le
  exact div_pos ((mul_pos hc hu).trans_le hV) hw

end ProphetSecretary.Limiting
