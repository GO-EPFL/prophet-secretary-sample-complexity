import ProphetSecretary.Statistics.MixedDataSelectedClockLoss
import ProphetSecretary.Statistics.DataSelectedClockLossIntegrability

/-!
# Genuine Fubini integrability of mixed selected-weight losses

One actual bounded-sample event supports all scalar choices and candidate values.
The independent candidate time is nonnegative almost surely. Both directions
therefore have the same auxiliary integrability bound, separately from the
statistical inverse-linear estimate.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.integrable_mixedDataSelectedClockLoss_pair (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ a, Z a∈Icc (0:ℝ) hi) (x : ℝ) :
    Integrable (fun qt => mixedDataSelectedClockLoss P known Z x qt.1 qt.2)
      (((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)).prod Instance.uniformClock) ∧
    Integrable (fun qt => mixedDataSelectedClockLossReverse P known Z x qt.1 qt.2)
      (((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)).prod Instance.uniformClock) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hm := measurable_mixedDataSelectedClockLoss_pair P known (P.integrable_maximum_of_bounded hbound) hZ (fun a => (hZrange a).1) x
  have hDataMP : MeasurePreserving (fun qt : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) => qt.1.1)
      (μ.prod Instance.uniformClock) (P.trainingCoordinateLaw k) :=
    (measurePreserving_fst (μ:=P.trainingCoordinateLaw k) (ν:=Instance.clocksLaw n)).comp measurePreserving_fst
  have htMP : MeasurePreserving (Prod.snd : ((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) → ℝ)
      (μ.prod Instance.uniformClock) Instance.uniformClock := measurePreserving_snd
  have hB : ∀ᵐ qt ∂μ.prod Instance.uniformClock,
      mixedDataSelectedClockLoss P known Z x qt.1 qt.2≤2+2*hi ∧ mixedDataSelectedClockLossReverse P known Z x qt.1 qt.2≤2+2*hi := by
    filter_upwards [hDataMP.quasiMeasurePreserving.ae (P.mixedDataSelectedClockLoss_pair_bounded (k:=k) known hbound hZrange x),
      htMP.quasiMeasurePreserving.ae uniformClock_nonnegative_ae] with qt hqt ht
    exact hqt qt.1.2 qt.2 ht
  constructor
  · apply Integrable.of_bound hm.1.aestronglyMeasurable (2+2*hi)
    exact hB.mono fun qt hqt => by
      change ‖mixedDataSelectedClockLoss P known Z x qt.1 qt.2‖≤_
      rw [Real.norm_eq_abs,abs_of_nonneg (mixedDataSelectedClockLoss_nonnegative _ _ _ _ _ _)]
      exact hqt.1
  · apply Integrable.of_bound hm.2.aestronglyMeasurable (2+2*hi)
    exact hB.mono fun qt hqt => by
      change ‖mixedDataSelectedClockLossReverse P known Z x qt.1 qt.2‖≤_
      rw [Real.norm_eq_abs,abs_of_nonneg (mixedDataSelectedClockLossReverse_nonnegative _ _ _ _ _ _)]
      exact hqt.2

/-- The candidate-value law is any probability law; the auxiliary bound does
not require bounded or positive candidate values. Statistical rate estimates
are applied separately on the true offer support. -/
theorem Instance.integrable_mixedDataSelectedClockLoss_pair_jointValue (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) {Z : ((Fin n × Fin k) → ℝ) → ℝ} {hi : ℝ}
    (hZ : Measurable Z) (hZrange : ∀ a, Z a∈Icc (0:ℝ) hi) (ρ : Measure ℝ) [IsProbabilityMeasure ρ] :
    Integrable (fun qxt => mixedDataSelectedClockLoss P known Z qxt.1.2 qxt.1.1 qxt.2)
      ((((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)).prod ρ).prod Instance.uniformClock) ∧
    Integrable (fun qxt => mixedDataSelectedClockLossReverse P known Z qxt.1.2 qxt.1.1 qxt.2)
      ((((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)).prod ρ).prod Instance.uniformClock) := by
  let μ := (P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)
  have hm := measurable_mixedDataSelectedClockLoss_pair_jointValue P known (P.integrable_maximum_of_bounded hbound) hZ (fun a => (hZrange a).1)
  have hDataMP : MeasurePreserving (fun qxt : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) => qxt.1.1.1)
      ((μ.prod ρ).prod Instance.uniformClock) (P.trainingCoordinateLaw k) :=
    (measurePreserving_fst (μ:=P.trainingCoordinateLaw k) (ν:=Instance.clocksLaw n)).comp
      ((measurePreserving_fst (μ:=μ) (ν:=ρ)).comp measurePreserving_fst)
  have htMP : MeasurePreserving (Prod.snd : (((((Fin n × Fin k) → ℝ) × (Fin n → ℝ)) × ℝ) × ℝ) → ℝ)
      ((μ.prod ρ).prod Instance.uniformClock) Instance.uniformClock := measurePreserving_snd
  have hB : ∀ᵐ qxt ∂(μ.prod ρ).prod Instance.uniformClock,
      mixedDataSelectedClockLoss P known Z qxt.1.2 qxt.1.1 qxt.2≤2+2*hi ∧ mixedDataSelectedClockLossReverse P known Z qxt.1.2 qxt.1.1 qxt.2≤2+2*hi := by
    filter_upwards [hDataMP.quasiMeasurePreserving.ae (P.paired_mixedClockGapLoss_bounded_ae (k:=k) known hbound hi),
      htMP.quasiMeasurePreserving.ae uniformClock_nonnegative_ae] with qxt hqt ht
    exact hqt (Z qxt.1.1.1) (hZrange qxt.1.1.1) qxt.1.1.2 qxt.1.2 qxt.2 ht
  constructor
  · apply Integrable.of_bound hm.1.aestronglyMeasurable (2+2*hi)
    exact hB.mono fun qxt hqt => by
      change ‖mixedDataSelectedClockLoss P known Z qxt.1.2 qxt.1.1 qxt.2‖≤_
      rw [Real.norm_eq_abs,abs_of_nonneg (mixedDataSelectedClockLoss_nonnegative _ _ _ _ _ _)]
      exact hqt.1
  · apply Integrable.of_bound hm.2.aestronglyMeasurable (2+2*hi)
    exact hB.mono fun qxt hqt => by
      change ‖mixedDataSelectedClockLossReverse P known Z qxt.1.2 qxt.1.1 qxt.2‖≤_
      rw [Real.norm_eq_abs,abs_of_nonneg (mixedDataSelectedClockLossReverse_nonnegative _ _ _ _ _ _)]
      exact hqt.2

end ProphetSecretary.Model
