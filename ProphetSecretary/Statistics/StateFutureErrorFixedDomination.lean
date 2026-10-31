import ProphetSecretary.Statistics.StateFutureErrorTransfer
import ProphetSecretary.Statistics.EmpiricalPendingValueMeasurability

/-!
# Actual fixed-prefix inheritance of future error domination

The child envelope's probability-one statement is transported by the proved
normalized reset law. A measurable fixed-time/scalar domination event then
transfers back through stationary resampling. No independence property of a
random child state is introduced as a hypothesis.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- For each fixed later time and scalar, the raw state-local error dominates
its actual later value error. A common all-parameter event is obtained later
by countable intersection and pathwise limits. -/
theorem Instance.stateFutureError_fixedLater_dominates (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi t₀ t z : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (ht₀0 : 0 ≤ t₀) (ht₀1 : t₀ < 1)
    (ht : t ∈ Icc t₀ 1) (hz : z ∈ Icc lo hi) :
    ∀ᵐ q ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n),
      |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
          (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z -
        P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (1-t) 1 z| ≤
      P.stateFutureError k lo hi t₀ q := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  let G : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) → ℝ := fun q =>
    |(totalEmpiricalInstance (reservoirCoordinates.symm q.1)).continuationValue
        (ProphetSecretary.Probability.pendingClockSet t q.2) (max 0 (1-t)) 1 z -
      P.continuationValue (ProphetSecretary.Probability.pendingClockSet t q.2) (max 0 (1-t)) 1 z|
  have hP := P.integrable_maximum_of_bounded hbound
  have hz0 : 0 ≤ z := hlo.trans hz.1
  have hMP := ProphetSecretary.Probability.restartTrainingClocks_measurePreserving (n := n)
    (P.trainingCoordinateLaw k) ht₀0 ht₀1
  have hSet : MeasurableSet {q | G q ≤ P.stateFutureError k lo hi t₀ q} :=
    measurableSet_le (P.measurable_pendingValueError t z hz0) (P.measurable_stateFutureError lo hi t₀)
  have hprod : ∀ᵐ qr ∂μ.prod μ,
      G (ProphetSecretary.Probability.restartTrainingClocks t₀ qr) ≤
        P.stateFutureError k lo hi t₀ (ProphetSecretary.Probability.restartTrainingClocks t₀ qr) := by
    apply (Measure.ae_prod_iff_ae_ae (hMP.measurable hSet)).mpr
    exact Eventually.of_forall fun q => by
      let A := ProphetSecretary.Probability.pendingClockSet t₀ q.2
      have hA : ∀ j, ∀ᵐ x ∂(P.restrictTo A).law j, x ≤ 1 := fun j => hbound (stateEmbedding A j)
      have hp := P.normalizedRefreshedStateCoordinates_measurePreserving (k := k) ht₀1 q.2
      have hdom := hp.quasiMeasurePreserving.ae
        ((P.restrictTo A).empiricalFutureError_dominates (k := k) hA
          (mul_nonneg hlo (sub_nonneg.mpr ht₀1.le))
          (mul_le_mul_of_nonneg_right hlohi (sub_nonneg.mpr ht₀1.le)))
      have hv : ∀ᵐ r ∂μ, ∀ i, 0 ≤ r.2 i :=
        (measurePreserving_snd (μ := P.trainingCoordinateLaw k) (ν := Instance.clocksLaw n)).quasiMeasurePreserving.ae
          ((Instance.clocks_mem_unitInterval (n := n)).mono fun _ h => fun i => (h i).1)
      filter_upwards [hdom,hv] with r hr hrv
      let q' := ProphetSecretary.Probability.restartTrainingClocks t₀ (q,r)
      have hA' : ProphetSecretary.Probability.pendingClockSet t₀ q'.2 = A :=
        ProphetSecretary.Probability.pendingClockSet_refresh ht₀1.le q.2 r.2 hrv
      have htransfer := P.stateFutureError_transfer hP hlo ht₀1 q' A hA' hr
      have h := htransfer t ht z hz
      change G q' ≤ _
      simpa only [G,max_eq_right (sub_nonneg.mpr ht.2)] using h
  have he := ae_map_iff (μ := μ.prod μ) hMP.measurable.aemeasurable hSet
  have hmap : Measure.map (ProphetSecretary.Probability.restartTrainingClocks t₀) (μ.prod μ) = μ := hMP.map_eq
  rw [hmap] at he
  have hmain := he.mpr hprod
  exact hmain.mono fun q hq => by
    simpa only [G,max_eq_right (sub_nonneg.mpr ht.2)] using hq

end ProphetSecretary.Model
