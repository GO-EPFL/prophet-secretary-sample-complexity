import ProphetSecretary.Probability.UnitSumChernoff
import ProphetSecretary.Model.TrainingCoordinates
import ProphetSecretary.Model.AllSamplesLearner

/-!
# The observable low/high first-moment classifier

The statistic is the actual sum of h independent full training rounds divided
by h. Selecting low uses only this statistic and the fixed public cutoff Sstar.
The hard sampling budget holds for every reservoir, including impossible data.
Paper correspondence: classifier in the large-first-moment subsection.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n h : ℕ}

noncomputable def firstMomentEstimate (a : (Fin n × Fin h) → ℝ) : ℝ :=
  (h:ℝ)⁻¹*ProphetSecretary.Probability.coordinateSum a

lemma measurable_firstMomentEstimate : Measurable (firstMomentEstimate (n:=n) (h:=h)) :=
  (Finset.measurable_sum Finset.univ (fun q _ => measurable_pi_apply q)).const_mul _

noncomputable def selectLowFirstMoment (Sstar : ℝ) (a : (Fin n × Fin h) → ℝ) : Bool :=
  if firstMomentEstimate a≤2*Sstar then true else false

lemma measurable_selectLowFirstMoment (Sstar : ℝ) :
    Measurable (selectLowFirstMoment (n:=n) (h:=h) Sstar) := by
  exact measurable_const.ite (measurableSet_le measurable_firstMomentEstimate measurable_const) measurable_const

lemma coordinateMeans_sum (P : Instance n) (h : ℕ) :
    (∑ q : Fin n × Fin h, ∫ x, x ∂P.law q.1)=(h:ℝ)*P.totalFirstMoment := by
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
  simp only [Instance.totalFirstMoment,Finset.mul_sum]

lemma firstMomentEstimate_le_iff (hh : 0<h) (a : (Fin n × Fin h) → ℝ) (Sstar : ℝ) :
    firstMomentEstimate a≤2*Sstar ↔ ProphetSecretary.Probability.coordinateSum a≤2*((h:ℝ)*Sstar) := by
  have hh' : (0:ℝ)<h := by exact_mod_cast hh
  rw [firstMomentEstimate,←div_eq_inv_mul,div_le_iff₀ hh']
  ring_nf

/-- Wrongly choosing high on the genuinely low class. The non-strict hypothesis
is slightly stronger than the displayed source claim. -/
theorem firstMomentClassifier_low_tail (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hh : 0<h) {Sstar : ℝ}
    (hS : 0≤Sstar) (hLow : P.totalFirstMoment≤Sstar) :
    (P.trainingCoordinateLaw h).real {a | selectLowFirstMoment Sstar a=false}≤
      Real.exp (-3*(h:ℝ)*Sstar/8) := by
  have hUnit (q : Fin n × Fin h) : ∀ᵐ x ∂P.law q.1, x∈Icc (0:ℝ) 1 := by
    filter_upwards [P.nonnegative q.1,hcap q.1] with x hx hx1
    exact ⟨hx,hx1⟩
  have hBound := ProphetSecretary.Probability.coordinateSum_upper_classifier_tail (fun q : Fin n × Fin h => P.law q.1)
    hUnit (mul_nonneg (Nat.cast_nonneg h) hS) (by
      rw [coordinateMeans_sum]
      exact mul_le_mul_of_nonneg_left hLow (Nat.cast_nonneg h))
  apply le_trans (b:=(P.trainingCoordinateLaw h).real {a | 2*((h:ℝ)*Sstar)≤ProphetSecretary.Probability.coordinateSum a})
  · refine measureReal_mono ?_ (measure_ne_top _ _)
    intro a ha
    have hA : ¬firstMomentEstimate a≤2*Sstar := by
      intro h
      simp only [Set.mem_setOf_eq,selectLowFirstMoment,if_pos h] at ha
      contradiction
    exact (lt_of_not_ge ((firstMomentEstimate_le_iff hh a Sstar).not.mp hA)).le
  · simpa only [Instance.trainingCoordinateLaw,mul_assoc] using hBound

/-- Wrongly choosing low on the genuinely high class. -/
theorem firstMomentClassifier_high_tail (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hh : 0<h) {Sstar : ℝ}
    (hS : 0≤Sstar) (hHigh : 3*Sstar≤P.totalFirstMoment) :
    (P.trainingCoordinateLaw h).real {a | selectLowFirstMoment Sstar a=true}≤
      Real.exp (-(h:ℝ)*Sstar/6) := by
  have hUnit (q : Fin n × Fin h) : ∀ᵐ x ∂P.law q.1, x∈Icc (0:ℝ) 1 := by
    filter_upwards [P.nonnegative q.1,hcap q.1] with x hx hx1
    exact ⟨hx,hx1⟩
  have hBound := ProphetSecretary.Probability.coordinateSum_lower_classifier_tail (fun q : Fin n × Fin h => P.law q.1)
    hUnit (mul_nonneg (Nat.cast_nonneg h) hS) (by
      rw [coordinateMeans_sum]
      nlinarith only [mul_le_mul_of_nonneg_left hHigh (Nat.cast_nonneg h)])
  have hEq : {a : (Fin n × Fin h) → ℝ | selectLowFirstMoment Sstar a=true}=
      {a | ProphetSecretary.Probability.coordinateSum a≤2*((h:ℝ)*Sstar)} := by
    ext a
    simp [selectLowFirstMoment,firstMomentEstimate_le_iff hh]
  rw [hEq]
  simpa only [Instance.trainingCoordinateLaw,neg_mul] using hBound

/-- The observable output is recovered from the causal transcript alone. -/
noncomputable def classifierFromTranscript (Sstar : ℝ) (H : Transcript n) : Bool :=
  selectLowFirstMoment Sstar (reservoirCoordinates (decodedReservoir (k:=h) H))

lemma measurable_classifierFromTranscript (Sstar : ℝ) :
    Measurable (classifierFromTranscript (n:=n) (h:=h) Sstar) :=
  (measurable_selectLowFirstMoment Sstar).comp
    (reservoirCoordinates.measurable.comp measurable_decodedReservoir)

lemma classifierFromTranscript_actual (Sstar : ℝ) (y : Reservoir n h) :
    classifierFromTranscript (h:=h) Sstar (trainingTranscript (requestAll h) () y)=
      selectLowFirstMoment Sstar (reservoirCoordinates y) := by
  unfold classifierFromTranscript
  rw [decodedReservoir_trainingTranscript]

lemma classifier_hardBudget (y : Reservoir n h) (i : Fin n) :
    requests (trainingTranscript (requestAll h) () y) i≤h := trainingTranscript_budget _ _ _ _

end ProphetSecretary.Statistics
