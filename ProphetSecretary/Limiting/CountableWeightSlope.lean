import ProphetSecretary.Limiting.CountableCanonicalLimit
import ProphetSecretary.Analysis.StableEnvelope
import ProphetSecretary.Limiting.NoReserve

/-!
# Stability of the scalar weight slope

The slope R−T is evaluated for a fixed admissible policy. Actual independent
seed erasure puts the canonical outcomes on the same experiment, and the
coupled outcome error bounds the difference of the expected slopes.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def RandomizedCountablePolicy.expectedWeightSlope {B : CountableInstance}
    (π : RandomizedCountablePolicy B) : ℝ := π.expectedReward-π.expectedDuration

lemma RandomizedCountablePolicy.expectedWeightSlope_abs_le {B : CountableInstance}
    (π : RandomizedCountablePolicy B) : |π.expectedWeightSlope|≤(B.cap : ℝ)+1 := by
  calc
    _ ≤ |π.expectedReward|+|π.expectedDuration| := abs_sub _ _
    _ = π.expectedReward+π.expectedDuration := by
      rw [abs_of_nonneg π.expectedReward_nonnegative,abs_of_nonneg π.expectedDuration_nonnegative]
    _ ≤ _ := add_le_add π.expectedReward_le_cap π.expectedDuration_le_one

lemma RandomizedCountablePolicy.expectedWeightSlope_difference_le {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    |π.expectedWeightSlope-(B.valuePolicy hw hc).expectedWeightSlope|≤π.expectedValueOutcomeError w c := by
  let π0 := B.valuePolicy hw hc
  let fR := fun v : CompleteWorld π.Seed =>
    (B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v)
  let fT := fun v : CompleteWorld π.Seed =>
    (B.valueRule w c).realizedDuration (eraseCompleteSeed v)
  have hMP := B.eraseCompleteSeed_measurePreserving π.seedLaw
  have hRI : Integrable fR (B.completeWorldLaw π.seedLaw) := hMP.integrable_comp_of_integrable π0.integrable_reward
  have hTI : Integrable fT (B.completeWorldLaw π.seedLaw) := hMP.integrable_comp_of_integrable π0.integrable_duration
  have hRMean : (∫ v, fR v ∂B.completeWorldLaw π.seedLaw)=π0.expectedReward :=
    hMP.hasLaw.integral_comp ((B.valueRule w c).measurable_realizedReward (B.valueRule_isMeasurable hw.le hc.le) B.terminal).aestronglyMeasurable
  have hTMean : (∫ v, fT v ∂B.completeWorldLaw π.seedLaw)=π0.expectedDuration :=
    hMP.hasLaw.integral_comp ((B.valueRule w c).measurable_realizedDuration (B.valueRule_isMeasurable hw.le hc.le)).aestronglyMeasurable
  let F := fun v : CompleteWorld π.Seed =>
    (π.rule.realizedReward B.terminal v-fR v)-(π.rule.realizedDuration v-fT v)
  have hExpr : π.expectedWeightSlope-π0.expectedWeightSlope=
      ∫ v, F v ∂B.completeWorldLaw π.seedLaw := by
    dsimp only [F]
    rw [integral_sub (f:=fun v => π.rule.realizedReward B.terminal v-fR v)
      (g:=fun v => π.rule.realizedDuration v-fT v) (π.integrable_reward.sub hRI) (π.integrable_duration.sub hTI),
      integral_sub (f:=π.rule.realizedReward B.terminal) (g:=fR) π.integrable_reward hRI,
      integral_sub (f:=π.rule.realizedDuration) (g:=fT) π.integrable_duration hTI,hRMean,hTMean]
    change (π.expectedReward-π.expectedDuration)-(π0.expectedReward-π0.expectedDuration)=
      (π.expectedReward-π0.expectedReward)-(π.expectedDuration-π0.expectedDuration)
    ring
  have hPoint (v : CompleteWorld π.Seed) : ‖F v‖≤π.rule.coupledValueOutcomeError B w c v := by
    change ‖(π.rule.realizedReward B.terminal v-fR v)-(π.rule.realizedDuration v-fT v)‖≤
      |π.rule.realizedReward B.terminal v-fR v|+|π.rule.realizedDuration v-fT v|
    simpa only [Real.norm_eq_abs] using norm_sub_le
      (π.rule.realizedReward B.terminal v-fR v) (π.rule.realizedDuration v-fT v)
  have hBound := norm_integral_le_of_norm_le
    (π.rule.integrable_coupledValueOutcomeError π.measurable_rule B π.seedLaw hw.le hc.le)
    (Filter.Eventually.of_forall hPoint)
  rw [hExpr]
  simpa only [Real.norm_eq_abs,RandomizedCountablePolicy.expectedValueOutcomeError] using hBound

end ProphetSecretary.Limiting
