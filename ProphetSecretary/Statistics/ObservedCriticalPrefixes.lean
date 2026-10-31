import ProphetSecretary.Statistics.StateFutureErrorConditioning
import ProphetSecretary.Model.TruncatedReward

/-!
# True-law critical prefixes are clock-history measurable

Only elapsed clock observations and true marginal laws determine the critical
value and remaining first moment. Independent training data is not used to
choose these events. These facts supply the observable multipliers for the
finite-grid entrance argument.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

variable {n : ℕ} {D : Type*} [mD : MeasurableSpace D]

lemma observedClockSigma_le (t : ℝ) : observedClockSigma D n t ≤
    (inferInstance : MeasurableSpace (D × (Fin n → ℝ))) :=
  ((measurable_censorClocks t).comp measurable_snd).comap_le

lemma observedClockSigma_mono {s t : ℝ} (hst : s ≤ t) : observedClockSigma D n s ≤ observedClockSigma D n t := by
  have htC : @Measurable (D × (Fin n → ℝ)) (Fin n → ℝ) (observedClockSigma D n t) MeasurableSpace.pi
      (fun q => censorClocks t q.2) := Measurable.of_comap_le le_rfl
  have hsC : @Measurable (D × (Fin n → ℝ)) (Fin n → ℝ) (observedClockSigma D n t) MeasurableSpace.pi
      (fun q => censorClocks s q.2) := by
    convert (measurable_censorClocks s).comp htC using 1
    funext q
    exact (censorClocks_comp hst q.2).symm
  exact hsC.comap_le

lemma pendingClockSet_censorClocks (t : ℝ) (u : Fin n → ℝ) :
    pendingClockSet t (censorClocks t u) = pendingClockSet t u := by
  apply Finset.ext
  intro i
  simp only [mem_pendingClockSet, censorClocks, le_min_iff, le_refl, and_true]

lemma measurable_pendingClockSet_observed (t : ℝ) :
    @Measurable (D × (Fin n → ℝ)) (Finset (Fin n)) (observedClockSigma D n t) _
      (fun q => pendingClockSet t q.2) := by
  have hC : @Measurable (D × (Fin n → ℝ)) (Fin n → ℝ) (observedClockSigma D n t) MeasurableSpace.pi
      (fun q => censorClocks t q.2) := Measurable.of_comap_le le_rfl
  have h := (measurable_pendingClockSet t).comp hC
  convert h using 1
  funext q
  exact (pendingClockSet_censorClocks t q.2).symm

end ProphetSecretary.Probability

namespace ProphetSecretary.Model

variable {n : ℕ} {D : Type*} [MeasurableSpace D]

lemma Instance.measurable_observedContinuationValue (P : Instance n) (t z : ℝ) :
    @Measurable (D × (Fin n → ℝ)) ℝ (ProphetSecretary.Probability.observedClockSigma D n t) _
      (fun q => P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z) :=
  (measurable_of_finite (fun A : Finset (Fin n) => P.continuationValue A (1-t) 1 z)).comp
    (ProphetSecretary.Probability.measurable_pendingClockSet_observed t)

lemma Instance.measurable_observedRemainingSize (P : Instance n) (t : ℝ) :
    @Measurable (D × (Fin n → ℝ)) ℝ (ProphetSecretary.Probability.observedClockSigma D n t) _
      (fun q => (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t q.2)).totalFirstMoment + (1-t)) :=
  (measurable_of_finite (fun A : Finset (Fin n) => (P.restrictTo A).totalFirstMoment + (1-t))).comp
    (ProphetSecretary.Probability.measurable_pendingClockSet_observed t)

lemma Instance.observedRemainingSize_mem (P : Instance n) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (u : Fin n → ℝ) :
    (P.restrictTo (ProphetSecretary.Probability.pendingClockSet t u)).totalFirstMoment + (1-t) ∈
      Icc (0 : ℝ) (P.totalFirstMoment + 1) := by
  constructor
  · exact add_nonneg (P.restrictTo _).totalFirstMoment_nonnegative (sub_nonneg.mpr ht1)
  · have h := P.totalFirstMoment_restrictTo_le (ProphetSecretary.Probability.pendingClockSet t u)
    linarith only [h, ht0]

end ProphetSecretary.Model
