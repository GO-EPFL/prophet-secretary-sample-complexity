import ProphetSecretary.Limiting.CountableCanonicalL1

/-!
# Coupled full-instance outcome error

The competing policy and the canonical rule use the same offers and arrival
times. The canonical rule ignores the competitor's independent auxiliary seed.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting
open CountableInstance

namespace CountableInstance

noncomputable def CountableRule.coupledValueOutcomeError {Seed : Type*} (π : CountableRule Seed)
    (B : CountableInstance) (w c : ℝ) (v : CompleteWorld Seed) : ℝ :=
  |π.realizedReward B.terminal v-(B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v)|+
  |π.realizedDuration v-(B.valueRule w c).realizedDuration (eraseCompleteSeed v)|

lemma CountableRule.coupledValueOutcomeError_nonnegative {Seed : Type*} (π : CountableRule Seed)
    (B : CountableInstance) (w c : ℝ) (v : CompleteWorld Seed) :
    0 ≤ π.coupledValueOutcomeError B w c v := add_nonneg (abs_nonneg _) (abs_nonneg _)

lemma CountableRule.measurable_coupledValueOutcomeError {Seed : Type*} [MeasurableSpace Seed]
    (π : CountableRule Seed) (hπ : π.IsMeasurable) (B : CountableInstance)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : Measurable (π.coupledValueOutcomeError B w c) := by
  have hErase : Measurable (eraseCompleteSeed (Seed := Seed)) := by
    exact measurable_fst.prodMk (measurable_snd.fst.prodMk (measurable_snd.snd.fst.prodMk measurable_const))
  have hValue := B.valueRule_isMeasurable hw hc
  have hReward := ((B.valueRule w c).measurable_realizedReward hValue B.terminal).comp hErase
  have hDuration := ((B.valueRule w c).measurable_realizedDuration hValue).comp hErase
  exact (continuous_abs.measurable.comp ((π.measurable_realizedReward hπ B.terminal).sub hReward)).add
    (continuous_abs.measurable.comp ((π.measurable_realizedDuration hπ).sub hDuration))

lemma CountableRule.coupledValueOutcomeError_bounded {Seed : Type*} [MeasurableSpace Seed]
    (π : CountableRule Seed) (B : CountableInstance) (w c : ℝ)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    ∀ᵐ v ∂B.completeWorldLaw ν, π.coupledValueOutcomeError B w c v ∈ Icc (0 : ℝ) ((B.cap : ℝ)+1) := by
  have hErase := B.eraseCompleteSeed_measurePreserving ν
  filter_upwards [π.reward_bounded B ν,
    hErase.quasiMeasurePreserving.ae ((B.valueRule w c).reward_bounded B (Measure.dirac ()))] with v hπ hV
  have hπT := π.duration_bounds v
  have hVT := (B.valueRule w c).duration_bounds (eraseCompleteSeed v)
  refine ⟨π.coupledValueOutcomeError_nonnegative B w c v,?_⟩
  have hR : |π.realizedReward B.terminal v-(B.valueRule w c).realizedReward B.terminal (eraseCompleteSeed v)| ≤ (B.cap : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith only [hπ.1,hπ.2,hV.1,hV.2]
  have hT : |π.realizedDuration v-(B.valueRule w c).realizedDuration (eraseCompleteSeed v)| ≤ (1 : ℝ) := by
    apply abs_le.mpr
    constructor <;> linarith only [hπT.1,hπT.2,hVT.1,hVT.2]
  exact add_le_add hR hT

lemma CountableRule.integrable_coupledValueOutcomeError {Seed : Type*} [MeasurableSpace Seed]
    (π : CountableRule Seed) (hπ : π.IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (π.coupledValueOutcomeError B w c) (B.completeWorldLaw ν) := by
  apply Integrable.of_bound (π.measurable_coupledValueOutcomeError hπ B hw hc).aestronglyMeasurable ((B.cap : ℝ)+1)
  filter_upwards [π.coupledValueOutcomeError_bounded B w c ν] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg hv.1]
  exact hv.2

end CountableInstance

noncomputable def RandomizedCountablePolicy.expectedValueOutcomeError {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) : ℝ :=
  ∫ v, π.rule.coupledValueOutcomeError B w c v ∂B.completeWorldLaw π.seedLaw

lemma RandomizedCountablePolicy.expectedValueOutcomeError_nonnegative {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (w c : ℝ) : 0 ≤ π.expectedValueOutcomeError w c :=
  integral_nonneg (π.rule.coupledValueOutcomeError_nonnegative B w c)

lemma RandomizedCountablePolicy.expectedValueOutcomeError_le_bound {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {H w c : ℝ}
    (hCap : (B.cap : ℝ) ≤ H) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    π.expectedValueOutcomeError w c ≤ H+1 := by
  have h := integral_mono_ae (π.rule.integrable_coupledValueOutcomeError π.measurable_rule B π.seedLaw hw hc)
    (integrable_const (H+1)) ((π.rule.coupledValueOutcomeError_bounded B w c π.seedLaw).mono
      (fun _ hv => hv.2.trans (add_le_add hCap le_rfl)))
  simpa only [RandomizedCountablePolicy.expectedValueOutcomeError,integral_const,probReal_univ,one_smul] using h

end ProphetSecretary.Limiting
