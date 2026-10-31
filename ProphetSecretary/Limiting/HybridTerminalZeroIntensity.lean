import ProphetSecretary.Limiting.HybridExcessState
import ProphetSecretary.Limiting.ZeroIntensity
import ProphetSecretary.Model.TerminalScalarValue

/-!
# Fixed terminal rewards at zero anonymous intensity

The actual configuration is empty almost surely. Supplying empty anonymous
history yields exactly an admissible finite policy, including its no-selection
terminal reward. Conversely every finite policy embeds by ignoring anonymous
arrivals. The value correspondence therefore holds for the full policy classes.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma emptyPoissonPolicy_terminalReward (π : RandomizedHybridPolicy n) (a : ℝ) (v : Model.World n π.Seed) :
    π.rule.realizedReward a (emptyConfiguration,v) = (emptyPoissonPolicy π).realizedTerminalReward a v := by
  have hx : combinedValues v.1 (fun j : Fin 0 => (Fin.elim0 j : Point)) = v.1 := by
    funext i
    induction i using Fin.addCases with
    | left i => simp only [combinedValues,Fin.addCases_left]; congr 1
    | right j => exact Fin.elim0 j
  have hu : combinedClocks v.2.1 (fun j : Fin 0 => (Fin.elim0 j : Point)) = v.2.1 := by
    funext i
    induction i using Fin.addCases with
    | left i => simp only [combinedClocks,Fin.addCases_left]; congr 1
    | right j => exact Fin.elim0 j
  unfold HybridRule.realizedReward HybridRule.reward HybridRule.HasSelection
  dsimp only [emptyConfiguration,configurationMk]
  erw [emptyPoissonPolicy_adapter,hx,hu]
  unfold Model.RandomizedPolicy.realizedTerminalReward Model.RandomizedPolicy.realizedReward
  split_ifs with h₁ h₂ h₂
  · rfl
  · exact False.elim (h₂ h₁)
  · exact False.elim (h₁ h₂)
  · rfl

lemma emptyPoissonPolicy_terminalScalarObjective (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity = 0) (w c : ℝ) :
    π.scalarObjective B w c = (emptyPoissonPolicy π).terminalScalarObjective B.individuals B.terminal w c := by
  let F : HybridWorld n π.Seed → ℝ := fun v => w * π.rule.realizedReward B.terminal v + c * π.rule.realizedDuration v
  have hm : Measurable F := ((π.rule.measurable_realizedReward π.measurable_rule B.terminal).const_mul w).add
    ((π.rule.measurable_realizedDuration π.measurable_rule).const_mul c)
  have hp := zeroIntensityWorld_measurePreserving B.individuals π.seedLaw
  have he := integral_map (μ := B.individuals.worldLaw π.seedLaw) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  unfold RandomizedHybridPolicy.scalarObjective
  change (∫ v, F v ∂hybridWorldLaw B.individuals B.intensity π.seedLaw) = _
  rw [hμ,he]
  unfold Model.RandomizedPolicy.terminalScalarObjective
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun v => by
    dsimp only [F]
    rw [emptyPoissonPolicy_terminalReward π B.terminal v,(emptyPoissonPolicy_outcomes π v).1]

lemma emptyPoissonPolicy_ignorePoisson (π : Model.RandomizedPolicy n) : emptyPoissonPolicy (ignorePoisson π) = π := by
  rfl

lemma FiniteIntensityHybridInstance.value_zeroIntensity_terminal (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c = Model.optimalTerminalScalarValue B.individuals B.terminal w c := by
  have hP := B.individuals.integrable_maximum_of_bounded B.individual_bounded
  apply le_antisymm
  · apply csSup_le (B.scalarPayoffs_nonempty w c)
    rintro y ⟨π,rfl⟩
    change π.scalarObjective B w c ≤ _
    rw [emptyPoissonPolicy_terminalScalarObjective π B hμ w c]
    exact le_csSup (Model.terminalScalarValues_bddAbove B.individuals hP B.terminal.property hw hc) ⟨emptyPoissonPolicy π,rfl⟩
  · apply csSup_le (Model.terminalScalarValues_nonempty B.individuals B.terminal w c)
    rintro y ⟨π,rfl⟩
    have he := emptyPoissonPolicy_terminalScalarObjective (ignorePoisson π) B hμ w c
    rw [emptyPoissonPolicy_ignorePoisson] at he
    exact he.symm.le.trans (B.scalarObjective_le_value (ignorePoisson π) w c)

lemma FiniteIntensityHybridInstance.excessState_intensity_zero (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity = 0) (a : ℝ≥0) : (B.excessState a).intensity = 0 := by
  apply FiniteMeasure.toMeasure_injective
  change (Model.excessLaw (B.intensity : Measure ℝ) a).restrict (Ioi 0) = 0
  rw [hμ]
  simp [Model.excessLaw]

lemma FiniteIntensityHybridInstance.value_reserveShift_zeroIntensity (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c = w * (B.terminal : ℝ) + (B.excessState B.terminal).optimalScalarValue w c := by
  have hE := (B.excessState B.terminal).value_zero_intensity (by rfl) (B.excessState_intensity_zero hμ B.terminal) hw.le hc
  have hF := Model.optimalTerminalScalarValue_eq_excessValue B.individuals
    (B.individuals.integrable_maximum_of_bounded B.individual_bounded) B.terminal.property hw hc
  calc
    B.optimalScalarValue w c = Model.optimalTerminalScalarValue B.individuals B.terminal w c :=
      B.value_zeroIntensity_terminal hμ hw hc
    _ = w * (B.terminal : ℝ) + Model.optimalScalarValue (B.individuals.excessOffers B.terminal) w c := hF
    _ = _ := congrArg (fun x : ℝ => w * (B.terminal : ℝ) + x) hE.symm

end ProphetSecretary.Limiting
