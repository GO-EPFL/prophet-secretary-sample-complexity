import ProphetSecretary.Limiting.CountableOutcomeError
import ProphetSecretary.Stability.Modulus

/-!
# Analytical square-integrable scores in the full stopping model

Scores may inspect the complete realized offers, including arrivals after
stopping. The actual coupled outcome bound controls their correlations without
making any score available to a competing policy.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def RandomizedCountablePolicy.coupledRewardDifference {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) (v : CompleteWorld π.Seed) : ℝ :=
  π.rule.realizedReward B.terminal v-(B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v)

noncomputable def RandomizedCountablePolicy.coupledDurationDifference {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) (v : CompleteWorld π.Seed) : ℝ :=
  π.rule.realizedDuration v-(B.valueRule w c).realizedDuration (eraseCompleteSeed v)

lemma RandomizedCountablePolicy.measurable_coupledDifferences {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (π.coupledRewardDifference w c) ∧ Measurable (π.coupledDurationDifference w c) := by
  have hErase : Measurable (eraseCompleteSeed (Seed := π.Seed)) :=
    measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk measurable_const))
  have hCanonical := B.valueRule_isMeasurable hw hc
  exact ⟨(π.rule.measurable_realizedReward π.measurable_rule B.terminal).sub
      (((B.valueRule w c).measurable_realizedReward hCanonical B.terminal).comp hErase),
    (π.rule.measurable_realizedDuration π.measurable_rule).sub
      (((B.valueRule w c).measurable_realizedDuration hCanonical).comp hErase)⟩

lemma RandomizedCountablePolicy.coupledDifferences_bounded {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) :
    (∀ᵐ v ∂B.completeWorldLaw π.seedLaw, |π.coupledRewardDifference w c v| ≤ (B.cap : ℝ)) ∧
    (∀ᵐ v ∂B.completeWorldLaw π.seedLaw, |π.coupledDurationDifference w c v| ≤ 1) := by
  have hSeed := B.eraseCompleteSeed_measurePreserving π.seedLaw
  have hBoth : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw,
      |π.coupledRewardDifference w c v| ≤ (B.cap : ℝ) ∧ |π.coupledDurationDifference w c v| ≤ 1 := by
    filter_upwards [π.rule.reward_bounded B π.seedLaw,
      hSeed.quasiMeasurePreserving.ae ((B.valueRule w c).reward_bounded B (Measure.dirac ()))] with v hR hC
    have hT := π.rule.duration_bounds v
    have hCT := (B.valueRule w c).duration_bounds (eraseCompleteSeed v)
    constructor
    · change |π.rule.realizedReward B.terminal v-(B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v)| ≤ _
      apply abs_le.mpr
      constructor <;> linarith only [hR.1,hR.2,hC.1,hC.2]
    · change |π.rule.realizedDuration v-(B.valueRule w c).realizedDuration (eraseCompleteSeed v)| ≤ _
      apply abs_le.mpr
      constructor <;> linarith only [hT.1,hT.2,hCT.1,hCT.2]
  exact ⟨hBoth.mono (fun _ h => h.1),hBoth.mono (fun _ h => h.2)⟩

theorem RandomizedCountablePolicy.score_stability {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {w c I W : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (score : CompleteWorld π.Seed → ℝ) (hScore : MemLp score 2 (B.completeWorldLaw π.seedLaw))
    (hInfo : (∫ v, score v^2 ∂B.completeWorldLaw π.seedLaw) ≤ I)
    (hMean : π.expectedValueOutcomeError w c ≤ W) :
    |∫ v, score v*π.coupledRewardDifference w c v ∂B.completeWorldLaw π.seedLaw|+
      |∫ v, score v*π.coupledDurationDifference w c v ∂B.completeWorldLaw π.seedLaw| ≤
        Real.sqrt (2*I*((B.cap : ℝ)+1)*W) := by
  have hm := π.measurable_coupledDifferences hw hc
  have hb := π.coupledDifferences_bounded w c
  exact ProphetSecretary.Stability.score_stability_bound_paper (B.completeWorldLaw π.seedLaw) B.cap.property
    hScore hm.1.aestronglyMeasurable hm.2.aestronglyMeasurable hb.1 hb.2 hInfo hMean

lemma RandomizedCountablePolicy.score_coupledDifferences_integrable {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    (score : CompleteWorld π.Seed → ℝ) (hScore : MemLp score 2 (B.completeWorldLaw π.seedLaw)) :
    Integrable (fun v => score v*π.coupledRewardDifference w c v) (B.completeWorldLaw π.seedLaw) ∧
    Integrable (fun v => score v*π.coupledDurationDifference w c v) (B.completeWorldLaw π.seedLaw) := by
  have hm := π.measurable_coupledDifferences hw hc
  have hb := π.coupledDifferences_bounded w c
  exact ProphetSecretary.Stability.score_products_integrable (B.completeWorldLaw π.seedLaw) hScore
    hm.1.aestronglyMeasurable hm.2.aestronglyMeasurable hb.1 hb.2

end ProphetSecretary.Limiting
