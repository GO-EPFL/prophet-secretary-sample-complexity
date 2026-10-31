import ProphetSecretary.Limiting.CountableValueMeanLimit
import ProphetSecretary.Limiting.HybridObserverPayoff

/-!
# Absolute outcome convergence of canonical truncations

The canonical truncations and the full canonical rule are executed on the
same online input. Almost-sure convergence and the common cap give convergence
in expected absolute reward and duration. Erasing an independent policy seed
preserves this input law.
-/

open MeasureTheory Set Filter
open scoped Topology Classical

namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def eraseCompleteSeed {Seed : Type*} (v : CompleteWorld Seed) : CompleteWorld Unit :=
  (v.1,(v.2.1,(v.2.2.1,())))

noncomputable def eraseHybridSeed {n : ℕ} {Seed : Type*} (v : HybridWorld n Seed) : HybridWorld n Unit :=
  (v.1,(v.2.1,(v.2.2.1,())))

lemma CountableInstance.eraseCompleteSeed_measurePreserving (B : CountableInstance)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (eraseCompleteSeed (Seed := Seed)) (B.completeWorldLaw ν)
      (B.completeWorldLaw (Measure.dirac ())) := by
  have hs : MeasurePreserving (fun _ : Seed => ()) ν (Measure.dirac ()) :=
    ⟨measurable_const,by simp [Measure.map_const]⟩
  exact (MeasurePreserving.id B.bandConfigurationsLaw).prod
    ((MeasurePreserving.id B.individualValuesLaw).prod
      ((MeasurePreserving.id CountableInstance.individualClocksLaw).prod hs))

lemma FiniteIntensityHybridInstance.eraseHybridSeed_measurePreserving {n : ℕ}
    (B : FiniteIntensityHybridInstance n) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (eraseHybridSeed (n := n) (Seed := Seed)) (B.law ν)
      (B.law (Measure.dirac ())) := by
  have hs : MeasurePreserving (fun _ : Seed => ()) ν (Measure.dirac ()) :=
    ⟨measurable_const,by simp [Measure.map_const]⟩
  exact (MeasurePreserving.id (configurationLaw B.intensity)).prod
    ((MeasurePreserving.id B.individuals.valuesLaw).prod
      ((MeasurePreserving.id (Model.Instance.clocksLaw n)).prod hs))

namespace CountableInstance

noncomputable def canonicalTruncationOutcomeError (B : CountableInstance) (N : ℕ)
    (w c : ℝ) (v : CompleteWorld Unit) : ℝ :=
  |(B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedReward B.terminal v-
    (B.valueRule w c).realizedReward B.terminal v|+
  |(B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedDuration v-
    (B.valueRule w c).realizedDuration v|

lemma measurable_canonicalTruncationOutcomeError (B : CountableInstance) (N : ℕ)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Measurable (B.canonicalTruncationOutcomeError N w c) := by
  have hRule := (B.truncatedValuePolicy N (B.markCutoff N) (B.terminal_lt_markCutoff N) hw hc).measurable_rule
  have hValue := B.valueRule_isMeasurable hw hc
  exact (continuous_abs.measurable.comp (((B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).measurable_realizedReward hRule B.terminal).sub
    ((B.valueRule w c).measurable_realizedReward hValue B.terminal))).add
      (continuous_abs.measurable.comp (((B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).measurable_realizedDuration hRule).sub
        ((B.valueRule w c).measurable_realizedDuration hValue)))

lemma canonicalTruncationOutcomeError_bounded (B : CountableInstance) (N : ℕ)
    (w c : ℝ) :
    ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      B.canonicalTruncationOutcomeError N w c v ∈ Icc (0 : ℝ) ((B.cap : ℝ)+1) := by
  filter_upwards [(B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).reward_bounded B (Measure.dirac ()),
    (B.valueRule w c).reward_bounded B (Measure.dirac ())] with v hN hV
  have hTN := (B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).duration_bounds v
  have hTV := (B.valueRule w c).duration_bounds v
  constructor
  · exact add_nonneg (abs_nonneg _) (abs_nonneg _)
  · have hR : |(B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedReward B.terminal v-
        (B.valueRule w c).realizedReward B.terminal v| ≤ (B.cap : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith only [hN.1,hN.2,hV.1,hV.2]
    have hT : |(B.truncatedValueRule N (B.markCutoff N) (B.terminal_lt_markCutoff N) w c).realizedDuration v-
        (B.valueRule w c).realizedDuration v| ≤ (1 : ℝ) := by
      apply abs_le.mpr
      constructor <;> linarith only [hTN.1,hTN.2,hTV.1,hTV.2]
    exact add_le_add hR hT

lemma integrable_canonicalTruncationOutcomeError (B : CountableInstance) (N : ℕ)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Integrable (B.canonicalTruncationOutcomeError N w c) (B.completeWorldLaw (Measure.dirac ())) := by
  apply Integrable.of_bound (B.measurable_canonicalTruncationOutcomeError N hw hc).aestronglyMeasurable ((B.cap : ℝ)+1)
  filter_upwards [B.canonicalTruncationOutcomeError_bounded N w c] with v hv
  rw [Real.norm_eq_abs,abs_of_nonneg hv.1]
  exact hv.2

lemma canonicalTruncationOutcomeError_tendsto_zero (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0 < w) (hc : 0 < c) :
    Tendsto (fun N => ∫ v, B.canonicalTruncationOutcomeError N w c v
      ∂B.completeWorldLaw (Measure.dirac ())) atTop (𝓝 (0 : ℝ)) := by
  have hMeas : ∀ᶠ N in atTop, AEStronglyMeasurable (B.canonicalTruncationOutcomeError N w c)
      (B.completeWorldLaw (Measure.dirac ())) := Eventually.of_forall fun N =>
    (B.measurable_canonicalTruncationOutcomeError N hw.le hc.le).aestronglyMeasurable
  have hBound : ∀ᶠ N in atTop, ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      ‖B.canonicalTruncationOutcomeError N w c v‖ ≤ (B.cap : ℝ)+1 := Eventually.of_forall fun N =>
    (B.canonicalTruncationOutcomeError_bounded N w c).mono (fun v hv => by
      rw [Real.norm_eq_abs,abs_of_nonneg hv.1]; exact hv.2)
  have hLimit : ∀ᵐ v ∂B.completeWorldLaw (Measure.dirac ()),
      Tendsto (fun N => B.canonicalTruncationOutcomeError N w c v) atTop (𝓝 (0 : ℝ)) := by
    filter_upwards [B.valueRule_truncation_outcomes_tendsto_ae hZero hw hc] with v hv
    have hR := (hv.1.sub_const ((B.valueRule w c).realizedReward B.terminal v)).abs
    have hT := (hv.2.sub_const ((B.valueRule w c).realizedDuration v)).abs
    simpa only [canonicalTruncationOutcomeError,sub_self,abs_zero,zero_add] using hR.add hT
  have h := tendsto_integral_filter_of_dominated_convergence
    (fun _ : CompleteWorld Unit => (B.cap : ℝ)+1) hMeas hBound (integrable_const _) hLimit
  simpa only [integral_zero] using h

end CountableInstance
end ProphetSecretary.Limiting
