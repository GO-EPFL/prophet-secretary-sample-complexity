import ProphetSecretary.Limiting.CountableOmissionL1
import ProphetSecretary.Limiting.OmissionObserverMatching
import ProphetSecretary.Limiting.CountableOutcomeError
import ProphetSecretary.Limiting.HybridOutcomeError

/-!
# Outcome comparison through a genuine finite truncation

On one analytical coupling, the old competitor, its causal omission simulator,
the finite canonical rule and the full canonical rule form a triangle of
actual outcomes. Equality of the middle canonical executions follows from
the same retained observer, including every retained zero identity.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

private lemma outcome_abs_triangle (a b c d : ℝ) :
    |a-d| ≤ |b-a|+|b-c|+|c-d| := by
  have h₁ := abs_sub_le a b d
  have h₂ := abs_sub_le b c d
  rw [abs_sub_comm a b] at h₁
  linarith only [h₁,h₂]

lemma RandomizedCountablePolicy.omission_outcome_triangle {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (hZero : B.terminal=0) (N : ℕ)
    {δ w c r : ℝ} (hδ : 0 < δ) (hwδ : δ ≤ w) (hcδ : δ ≤ c)
    (hNear : B.optimalScalarValue w c-π.scalarObjective w c ≤ r) :
    let b := B.markCutoff N
    let hb := B.terminal_lt_markCutoff N
    let C := B.truncation N b hb
    let σ := π.simulateOmissions N b
    π.expectedValueOutcomeError w c ≤ (2*r+3*w*B.omissionError N b)/δ+
      σ.expectedValueOutcomeError C w c+
      (∫ v, B.canonicalTruncationOutcomeError N w c v ∂B.completeWorldLaw (Measure.dirac ())) := by
  let b := B.markCutoff N
  have hb := B.terminal_lt_markCutoff N
  let C := B.truncation N b hb
  let σ := π.simulateOmissions N b
  letI : IsProbabilityMeasure (σ.seedLaw : Measure (OmissionAux π.Seed)) := σ.probability
  have hw : 0 < w := hδ.trans_le hwδ
  have hc : 0 < c := hδ.trans_le hcδ
  obtain ⟨Γ,hΓ,hNew,hOld,hHist,hPerf⟩ := π.exists_omission_performance_observer_coupling N hb
  letI : IsProbabilityMeasure Γ := hΓ
  let Dᵣ := fun q : OmissionExecutionWorld π.Seed =>
    |σ.rule.realizedReward B.terminal (newExecutionWorld N q)-π.rule.realizedReward B.terminal (oldExecutionWorld q)|
  let Dₜ := fun q : OmissionExecutionWorld π.Seed =>
    |σ.rule.realizedDuration (newExecutionWorld N q)-π.rule.realizedDuration (oldExecutionWorld q)|
  let E₀ := fun q : OmissionExecutionWorld π.Seed => π.rule.coupledValueOutcomeError B w c (oldExecutionWorld q)
  let E₁ := fun q : OmissionExecutionWorld π.Seed => σ.rule.coupledValueOutcomeError C w c (newExecutionWorld N q)
  let E₂ := fun q : OmissionExecutionWorld π.Seed => B.canonicalTruncationOutcomeError N w c (eraseCompleteSeed (oldExecutionWorld q))
  have hOldUnit := (B.eraseCompleteSeed_measurePreserving π.seedLaw).comp hOld
  have hDᵣI : Integrable Dᵣ Γ := ((hNew.integrable_comp_of_integrable (σ.integrable_reward C)).sub
    (hOld.integrable_comp_of_integrable π.integrable_reward)).abs
  have hDₜI : Integrable Dₜ Γ := ((hNew.integrable_comp_of_integrable (σ.integrable_duration C)).sub
    (hOld.integrable_comp_of_integrable π.integrable_duration)).abs
  have hE₀I : Integrable E₀ Γ := hOld.integrable_comp_of_integrable
    (π.rule.integrable_coupledValueOutcomeError π.measurable_rule B π.seedLaw hw.le hc.le)
  have hE₁I : Integrable E₁ Γ := hNew.integrable_comp_of_integrable
    (σ.rule.integrable_coupledValueOutcomeError σ.measurable_rule C σ.seedLaw hw.le hc.le)
  have hE₂I : Integrable E₂ Γ := hOldUnit.integrable_comp_of_integrable
    (B.integrable_canonicalTruncationOutcomeError N hw.le hc.le)
  have hMatch := @omission_truncated_payoffs_match_ae B π.Seed π.seedSpace π.seedLaw π.probability
    N b hb Γ hΓ σ.seedLaw σ.probability hNew hOld hHist
    (C.valueRule w c) (C.valueRule_isMeasurable hw.le hc.le)
  have hPoint : ∀ᵐ q ∂Γ, E₀ q ≤ Dᵣ q+Dₜ q+E₁ q+E₂ q := by
    filter_upwards [hMatch] with q hq
    have hFinite := σ.rule.coupledValueOutcomeError_eq_actual C hZero w c (newExecutionWorld N q)
    have hR := outcome_abs_triangle
      (π.rule.realizedReward B.terminal (oldExecutionWorld q))
      (σ.rule.realizedReward B.terminal (newExecutionWorld N q))
      ((C.valueRule w c).realizedReward B.terminal (eraseHybridSeed (newExecutionWorld N q)))
      ((B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed (oldExecutionWorld q)))
    have hT := outcome_abs_triangle
      (π.rule.realizedDuration (oldExecutionWorld q))
      (σ.rule.realizedDuration (newExecutionWorld N q))
      ((C.valueRule w c).realizedDuration (eraseHybridSeed (newExecutionWorld N q)))
      ((B.valueRule w c).realizedDuration (eraseCompleteSeed (oldExecutionWorld q)))
    have hqT := hq.1
    have hqR := hq.2
    change (B.truncatedValueRule N b hb w c).realizedDuration (eraseCompleteSeed (oldExecutionWorld q)) =
      (C.valueRule w c).realizedDuration (eraseHybridSeed (newExecutionWorld N q)) at hqT
    change (B.truncatedValueRule N b hb w c).realizedReward B.terminal (eraseCompleteSeed (oldExecutionWorld q)) =
      (C.valueRule w c).realizedReward B.terminal (eraseHybridSeed (newExecutionWorld N q)) at hqR
    rw [← hqR] at hR
    rw [← hqT] at hT
    change E₁ q =
      |σ.rule.realizedReward B.terminal (newExecutionWorld N q)-
        (C.valueRule w c).realizedReward B.terminal (eraseHybridSeed (newExecutionWorld N q))|+
      |σ.rule.realizedDuration (newExecutionWorld N q)-
        (C.valueRule w c).realizedDuration (eraseHybridSeed (newExecutionWorld N q))| at hFinite
    rw [← hqR,← hqT] at hFinite
    dsimp only [b] at hR hT hFinite
    rw [hFinite]
    dsimp only [E₀,Dᵣ,Dₜ,E₂,CountableRule.coupledValueOutcomeError,canonicalTruncationOutcomeError]
    nlinarith only [hR,hT]
  have hInt := integral_mono_ae hE₀I (((hDᵣI.add hDₜI).add hE₁I).add hE₂I) hPoint
  change (∫ q, E₀ q ∂Γ) ≤ ∫ q, Dᵣ q+Dₜ q+E₁ q+E₂ q ∂Γ at hInt
  rw [integral_add (f := fun q => Dᵣ q+Dₜ q+E₁ q) (g := E₂) ((hDᵣI.add hDₜI).add hE₁I) hE₂I,
    integral_add (f := fun q => Dᵣ q+Dₜ q) (g := E₁) (hDᵣI.add hDₜI) hE₁I,
    integral_add hDᵣI hDₜI] at hInt
  have hE₀ := hOld.hasLaw.integral_comp
    (π.rule.measurable_coupledValueOutcomeError π.measurable_rule B hw.le hc.le).aestronglyMeasurable
  have hE₁ := hNew.hasLaw.integral_comp
    (σ.rule.measurable_coupledValueOutcomeError σ.measurable_rule C hw.le hc.le).aestronglyMeasurable
  have hE₂ := hOldUnit.hasLaw.integral_comp
    (B.measurable_canonicalTruncationOutcomeError N hw.le hc.le).aestronglyMeasurable
  change (∫ q, E₀ q ∂Γ) = π.expectedValueOutcomeError w c at hE₀
  change (∫ q, E₁ q ∂Γ) = σ.expectedValueOutcomeError C w c at hE₁
  change (∫ q, E₂ q ∂Γ) = ∫ v, B.canonicalTruncationOutcomeError N w c v
    ∂B.completeWorldLaw (Measure.dirac ()) at hE₂
  rw [hE₀,hE₁,hE₂] at hInt
  have hL1 := π.omission_coupled_l1_bounds N hb hw.le hc.le hNear Γ hNew hOld hPerf
  have hR0 : 0 ≤ ∫ q, Dᵣ q ∂Γ := integral_nonneg (fun _ => abs_nonneg _)
  have hT0 : 0 ≤ ∫ q, Dₜ q ∂Γ := integral_nonneg (fun _ => abs_nonneg _)
  have hRW := mul_le_mul_of_nonneg_right hwδ hR0
  have hTC := mul_le_mul_of_nonneg_right hcδ hT0
  have hSumError : (∫ q, Dᵣ q ∂Γ)+(∫ q, Dₜ q ∂Γ) ≤ (2*r+3*w*B.omissionError N b)/δ := by
    apply (le_div_iff₀ hδ).mpr
    have hL1T : c*(∫ q, Dₜ q ∂Γ) ≤ r+w*B.omissionError N b := hL1.1
    have hL1R : w*(∫ q, Dᵣ q ∂Γ) ≤ r+2*w*B.omissionError N b := hL1.2
    nlinarith only [hL1T,hL1R,hRW,hTC]
  exact hInt.trans (add_le_add (add_le_add hSumError le_rfl) le_rfl)

end ProphetSecretary.Limiting
