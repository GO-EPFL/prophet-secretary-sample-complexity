import ProphetSecretary.Limiting.OmissionOutcomeComparison
import ProphetSecretary.Limiting.OmissionTailLevel

/-!
# Reward and duration comparison on the constructed coupling

Every premise of the pathwise deletion comparison is discharged from the
actual online marginals: original admissibility, independent-clock regularity,
nonnegative bounded values, exact past reconstruction, and the omitted maximum.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

lemma RandomizedCountablePolicy.omission_performance_ae_of_coupling {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b)
    (Γ : Measure (OmissionExecutionWorld π.Seed)) [IsProbabilityMeasure Γ]
    (hNew : MeasurePreserving (newExecutionWorld N) Γ
      ((B.truncation N b hb).law (π.simulateOmissions N b).seedLaw))
    (hOld : MeasurePreserving oldExecutionWorld Γ (B.completeWorldLaw π.seedLaw))
    (hHist : ∀ᵐ q ∂Γ, bandCountingMeasure q.1.2 = joinedCloud q.1.1 ∧ LowCloudRegular B b q.1.1.2) :
    ∀ᵐ q ∂Γ,
      π.rule.realizedDuration (oldExecutionWorld q) ≤
        (π.simulateOmissions N b).rule.realizedDuration (newExecutionWorld N q) ∧
      π.rule.realizedReward B.terminal (oldExecutionWorld q) ≤
        (π.simulateOmissions N b).rule.realizedReward B.terminal (newExecutionWorld N q) +
          (B.individualTailExcessMaximum N (oldExecutionWorld q).2.1 + (b-(B.terminal : ℝ))) := by
  let σ := π.simulateOmissions N b
  have hN : MeasurePreserving (newExecutionWorld N) Γ ((B.truncation N b hb).law σ.seedLaw) := hNew
  have hValueOld : MeasurePreserving (fun v : CompleteWorld π.Seed => v.2.1)
      (B.completeWorldLaw π.seedLaw) B.individualValuesLaw := measurePreserving_fst.comp measurePreserving_snd
  have hValues : MeasurePreserving (fun q : OmissionExecutionWorld π.Seed => (oldExecutionWorld q).2.1) Γ
      B.individualValuesLaw := hValueOld.comp hOld
  have hClockNew := hybrid_combined_clocks_regular (B.truncation N b hb).individuals
    (B.truncation N b hb).intensity σ.seedLaw
  have hValuesNew := realized_values_bounds (B.truncation N b hb).individuals
    (B.truncation N b hb).intensity σ.seedLaw (B.truncation N b hb).individual_bounded (B.truncation N b hb).intensity_supported
  filter_upwards [hHist,hOld.quasiMeasurePreserving.ae π.admissible,
    hOld.quasiMeasurePreserving.ae (B.codeValue_bounded π.seedLaw),
    hOld.quasiMeasurePreserving.ae (B.present_candidate_times_injective π.seedLaw),
    hValues.quasiMeasurePreserving.ae B.individual_values_supported,
    hN.quasiMeasurePreserving.ae hClockNew,hN.quasiMeasurePreserving.ae hValuesNew]
      with q hHist hFirst hOldNN hOldClock hX hNewClock hNewNN
  have hInj : Set.InjOn (codeTime (oldExecutionWorld q)) {i | π.rule.codeAccepted (oldExecutionWorld q) i} := by
    intro i hi j hj he
    have hci : candidatePresent (oldExecutionWorld q) (candidateEnumeration.symm i) := hi.1
    have hcj : candidatePresent (oldExecutionWorld q) (candidateEnumeration.symm j) := hj.1
    have ht : (candidatePoint (oldExecutionWorld q) (candidateEnumeration.symm i)).1 =
        (candidatePoint (oldExecutionWorld q) (candidateEnumeration.symm j)).1 := he
    exact candidateEnumeration.symm.injective (hOldClock hci hcj ht)
  have hu (k) : combinedClocks (newExecutionWorld N q).2.2.1 (newExecutionWorld N q).1.2 k ∈ Icc (0 : ℝ) 1 :=
    ⟨(hNewClock.2 k).1.le,(hNewClock.2 k).2.le⟩
  let e := B.individualTailExcessMaximum N (oldExecutionWorld q).2.1
  have he0 : 0 ≤ e := (B.individualTailExcessMaximum_bounds_of_cap N _ (fun j => (hX j).2)).1
  have hbd : b ≤ e+b := le_add_of_nonneg_left he0
  have had : (B.terminal : ℝ) ≤ e+b := hb.le.trans hbd
  have hTail (j : ℕ) (hj : N ≤ j) : (oldExecutionWorld q).2.1 j ≤ e+b :=
    (B.individual_value_le_tail_level N _ (fun k => (hX k).2) j hj).trans (add_le_add le_rfl hb.le)
  have hD := omission_realized_duration_le B π.rule π.measurable_rule N q hHist.1 hHist.2 hFirst hu
  have hR := omission_realized_reward_le B π.rule π.measurable_rule N q hHist.1 hHist.2 had hbd hTail
    hFirst (fun i hi => (hOldNN i hi.1).1) hInj hu (fun k => (hNewNN k).1) hNewClock.1
  refine ⟨hD,?_⟩
  change π.rule.realizedReward B.terminal (oldExecutionWorld q) ≤
    (simulateOmittedRule B π.rule N).realizedReward B.terminal (newExecutionWorld N q) + (e+(b-(B.terminal : ℝ)))
  have heq : (e+b)-(B.terminal : ℝ) = e+(b-(B.terminal : ℝ)) := by ring
  rw [heq] at hR
  exact hR

lemma RandomizedCountablePolicy.exists_omission_performance_coupling {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    let σ := π.simulateOmissions N b
    ∃ Γ : Measure (OmissionExecutionWorld π.Seed), IsProbabilityMeasure Γ ∧
      MeasurePreserving (newExecutionWorld N) Γ ((B.truncation N b hb).law σ.seedLaw) ∧
      MeasurePreserving oldExecutionWorld Γ (B.completeWorldLaw π.seedLaw) ∧
      (∀ᵐ q ∂Γ,
        π.rule.realizedDuration (oldExecutionWorld q) ≤ σ.rule.realizedDuration (newExecutionWorld N q) ∧
        π.rule.realizedReward B.terminal (oldExecutionWorld q) ≤ σ.rule.realizedReward B.terminal (newExecutionWorld N q) +
          (B.individualTailExcessMaximum N (oldExecutionWorld q).2.1 + (b-(B.terminal : ℝ)))) := by
  obtain ⟨Γ,hΓ,hNew,hOld,hHist⟩ := exists_omissionExecution_coupling B π.seedLaw N hb
  letI : IsProbabilityMeasure Γ := hΓ
  exact ⟨Γ,hΓ,hNew,hOld,π.omission_performance_ae_of_coupling N hb Γ hNew hOld hHist⟩

lemma RandomizedCountablePolicy.exists_omission_performance_observer_coupling {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (N : ℕ) {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    let σ := π.simulateOmissions N b
    ∃ Γ : Measure (OmissionExecutionWorld π.Seed), IsProbabilityMeasure Γ ∧
      MeasurePreserving (newExecutionWorld N) Γ ((B.truncation N b hb).law σ.seedLaw) ∧
      MeasurePreserving oldExecutionWorld Γ (B.completeWorldLaw π.seedLaw) ∧
      (∀ᵐ q ∂Γ, bandCountingMeasure q.1.2 = joinedCloud q.1.1 ∧ LowCloudRegular B b q.1.1.2) ∧
      (∀ᵐ q ∂Γ,
        π.rule.realizedDuration (oldExecutionWorld q) ≤ σ.rule.realizedDuration (newExecutionWorld N q) ∧
        π.rule.realizedReward B.terminal (oldExecutionWorld q) ≤ σ.rule.realizedReward B.terminal (newExecutionWorld N q) +
          (B.individualTailExcessMaximum N (oldExecutionWorld q).2.1 + (b-(B.terminal : ℝ)))) := by
  obtain ⟨Γ,hΓ,hNew,hOld,hHist⟩ := exists_omissionExecution_coupling B π.seedLaw N hb
  letI : IsProbabilityMeasure Γ := hΓ
  exact ⟨Γ,hΓ,hNew,hOld,hHist,π.omission_performance_ae_of_coupling N hb Γ hNew hOld hHist⟩

end ProphetSecretary.Limiting
