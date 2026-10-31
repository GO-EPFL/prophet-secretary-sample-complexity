import ProphetSecretary.Limiting.CountableCanonicalL1
import ProphetSecretary.Limiting.OmissionPerformanceFacts

/-!
# The same retained observer on the actual omission coupling

The old high-mark counting measure is exactly the new finite configuration.
Retained identities and clocks agree pointwise, including their zero values.
Consequently every fixed truncated rule has the same reward and duration in
the two executions. Its callbacks still receive only the strict observed past.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma omission_high_countingMeasure_eq (B : CountableInstance) {Seed : Type*}
    (q : OmissionExecutionWorld Seed) {b : ℝ}
    (hCount : bandCountingMeasure q.1.2 = joinedCloud q.1.1)
    (hLow : LowCloudRegular B b q.1.1.2)
    (hHigh : ∀ j : Fin q.1.1.1.1, b < (q.1.1.1.2 j).2) :
    (bandCountingMeasure q.1.2).restrict (univ ×ˢ Ioi b) = countingMeasure q.1.1.1 := by
  have hLowZero : q.1.1.2 (univ ×ˢ Ioi b) = 0 := by
    apply measure_mono_null _ hLow.1
    intro p hp hn
    exact (not_lt_of_ge hn.2.2) hp.2
  have hHighSelf : (countingMeasure q.1.1.1).restrict (univ ×ˢ Ioi b) = countingMeasure q.1.1.1 := by
    rw [restricted_countingMeasure _ (MeasurableSet.univ.prod measurableSet_Ioi)]
    apply Finset.sum_congr rfl
    intro j _
    exact if_pos ⟨mem_univ _,hHigh j⟩
  rw [hCount,joinedCloud,Measure.restrict_add,hHighSelf,Measure.restrict_eq_zero.mpr hLowZero,add_zero]

lemma omission_unit_observer_eq (N : ℕ) {Seed : Type*} (q : OmissionExecutionWorld Seed)
    {b : ℝ} (hFinite : (finiteCutoffCountingMeasure b q.1.2 : Measure Point) =
      (bandCountingMeasure q.1.2).restrict (univ ×ˢ Ioi b))
    (hHigh : (bandCountingMeasure q.1.2).restrict (univ ×ˢ Ioi b) = countingMeasure q.1.1.1) :
    truncatedObserverWorld (N := N) (finiteCutoffCountingMeasure b (oldExecutionWorld q).1)
      (eraseCompleteSeed (oldExecutionWorld q)) =
      hybridObserverWorld (eraseHybridSeed (newExecutionWorld N q)) := by
  have hMeasures : finiteCutoffCountingMeasure b q.1.2 = configurationFiniteMeasure q.1.1.1 := by
    apply Subtype.ext
    exact hFinite.trans (hHigh.trans (configurationFiniteMeasure_coe _).symm)
  change (finiteCutoffCountingMeasure b q.1.2,
    ((fun i : Fin N => q.2.1 i.val),((fun i : Fin N => q.2.2.1 i.val),()))) =
      (configurationFiniteMeasure q.1.1.1,
        ((splitCoordinates N q.2.1).1,((splitCoordinates N q.2.2.1).1,())))
  rw [hMeasures]
  rfl

lemma omission_truncated_payoffs_match_ae (B : CountableInstance) {Seed : Type*}
    [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b)
    (Γ : Measure (OmissionExecutionWorld Seed)) [IsProbabilityMeasure Γ]
    (ξ : Measure (OmissionAux Seed)) [IsProbabilityMeasure ξ]
    (hNew : MeasurePreserving (newExecutionWorld N) Γ ((B.truncation N b hb).law ξ))
    (hOld : MeasurePreserving oldExecutionWorld Γ (B.completeWorldLaw ν))
    (hHist : ∀ᵐ q ∂Γ, bandCountingMeasure q.1.2 = joinedCloud q.1.1 ∧ LowCloudRegular B b q.1.1.2)
    (ρ : HybridRule N Unit) (hρ : ρ.IsMeasurable) :
    ∀ᵐ q ∂Γ,
      (extendTruncatedRule ρ b).realizedDuration (eraseCompleteSeed (oldExecutionWorld q)) =
        ρ.realizedDuration (eraseHybridSeed (newExecutionWorld N q)) ∧
      (extendTruncatedRule ρ b).realizedReward B.terminal (eraseCompleteSeed (oldExecutionWorld q)) =
        ρ.realizedReward B.terminal (eraseHybridSeed (newExecutionWorld N q)) := by
  let C := B.truncation N b hb
  have hOldUnit := (B.eraseCompleteSeed_measurePreserving ν).comp hOld
  have hNewUnit := (C.eraseHybridSeed_measurePreserving ξ).comp hNew
  have hConfig : MeasurePreserving (fun q : OmissionExecutionWorld Seed => q.1.1.1) Γ
      (configurationLaw (B.intensityAbove b hb)) :=
    (measurePreserving_fst : MeasurePreserving (Prod.fst : HybridWorld N (OmissionAux Seed) → Configuration)
      (C.law ξ) (configurationLaw C.intensity)).comp hNew
  have hFinite := (measurePreserving_fst : MeasurePreserving (Prod.fst : CompleteWorld Seed → BandConfigurations)
    (B.completeWorldLaw ν) B.bandConfigurationsLaw).comp hOld
  filter_upwards [hHist,
    hConfig.quasiMeasurePreserving.ae (B.intensityAbove_configuration_marks hb),
    hFinite.quasiMeasurePreserving.ae (B.finiteCutoffCountingMeasure_coe_ae hb),
    hOldUnit.quasiMeasurePreserving.ae (ρ.extended_payoffs_eq_observable hρ B (Measure.dirac ()) hb),
    hNewUnit.quasiMeasurePreserving.ae (ρ.hybrid_payoffs_eq_observable hρ C (Measure.dirac ()))]
      with q hq hHigh hFinite hOldPay hNewPay
  have hObs := omission_unit_observer_eq N q hFinite (omission_high_countingMeasure_eq B q hq.1 hq.2 hHigh)
  change ρ.observableDuration
      (truncatedObserverWorld (finiteCutoffCountingMeasure b (oldExecutionWorld q).1) (eraseCompleteSeed (oldExecutionWorld q))) =
      (extendTruncatedRule ρ b).realizedDuration (eraseCompleteSeed (oldExecutionWorld q)) ∧
    ρ.observableReward B.terminal
      (truncatedObserverWorld (finiteCutoffCountingMeasure b (oldExecutionWorld q).1) (eraseCompleteSeed (oldExecutionWorld q))) =
      (extendTruncatedRule ρ b).realizedReward B.terminal (eraseCompleteSeed (oldExecutionWorld q)) at hOldPay
  rw [hObs] at hOldPay
  exact ⟨hOldPay.1.symm.trans hNewPay.1,hOldPay.2.symm.trans hNewPay.2⟩

end ProphetSecretary.Limiting
