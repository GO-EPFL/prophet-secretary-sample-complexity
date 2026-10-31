import ProphetSecretary.Limiting.CountableHorizonExecution
import ProphetSecretary.Limiting.CountableCanonicalReach
import ProphetSecretary.Limiting.CountableClockNullSets

/-!
# Physical-horizon reach and selection comparisons

The physical experiment scales every complete clock by the positive horizon.
Its observed callbacks, accepted codes and actual first acceptance have already
been transported. Reach and selection probabilities are unchanged, while mean
duration is multiplied by the horizon. Independent physical clocks have the
explicit normalized Lebesgue law on that horizon.
-/
open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*} [MeasurableSpace Seed]

noncomputable def scaledUniformClock (h : ℝ) : Measure ℝ :=
  Model.Instance.uniformClock.map (fun t => h*t)

instance scaledUniformClock_probability (h : ℝ) : IsProbabilityMeasure (scaledUniformClock h) :=
  Measure.isProbabilityMeasure_map (measurable_id.const_mul h).aemeasurable

lemma completeWorld_physical_clocks_map (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (h : ℝ) :
    (B.completeWorldLaw ν).map (fun v : CompleteWorld Seed => fun i => h*v.2.2.1 i)=
      Measure.infinitePi (fun _ : ℕ => scaledUniformClock h) := by
  have hU : Measurable (fun v : CompleteWorld Seed => v.2.2.1) :=
    measurable_fst.comp (measurable_snd.comp measurable_snd)
  have hEval (i : ℕ) : Measurable (fun u : ℕ → ℝ => u i) := measurable_pi_apply i
  have hMul : Measurable (fun t : ℝ => h*t) := measurable_id.const_mul h
  have hScale : Measurable (fun u : ℕ → ℝ => fun i => h*u i) :=
    measurable_pi_lambda _ (fun i => (hEval i).const_mul h)
  calc
    _ = ((B.completeWorldLaw ν).map (fun v : CompleteWorld Seed => v.2.2.1)).map
        (fun u : ℕ → ℝ => fun i => h*u i) := (Measure.map_map hScale hU).symm
    _ = individualClocksLaw.map (fun u : ℕ → ℝ => fun i => h*u i) := by
      rw [(B.individualClocks_completeWorld_measurePreserving ν).map_eq]
    _ = _ := Measure.infinitePi_map_pi (fun _ : ℕ => Model.Instance.uniformClock) (fun _ => hMul)

lemma completeWorld_physical_clock_map (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {h : ℝ} (hh : 0 < h) (i : ℕ) :
    (B.completeWorldLaw ν).map (fun v : CompleteWorld Seed => h*v.2.2.1 i)=
      ENNReal.ofReal h⁻¹ • volume.restrict (Icc (0 : ℝ) h) := by
  have hU : Measurable (fun v : CompleteWorld Seed => v.2.2.1 i) :=
    (individualClock_completeWorld_measurePreserving B ν i).measurable
  have hMul : Measurable (fun t : ℝ => h*t) := measurable_id.const_mul h
  calc
    _ = ((B.completeWorldLaw ν).map (fun v : CompleteWorld Seed => v.2.2.1 i)).map
        (fun t : ℝ => h*t) := (Measure.map_map hMul hU).symm
    _ = _ := by rw [(individualClock_completeWorld_measurePreserving B ν i).map_eq,Model.scaled_uniformClock_eq hh]

def CountableRule.AdmissibleAt (π : CountableRule Seed) (B : CountableInstance)
    (ν : Measure Seed) (h : ℝ) : Prop :=
  ∀ᵐ v ∂B.completeWorldLaw ν,
    FirstAcceptance.HasFirstIfAccepted (π.codeAcceptedAt h) codeTime (scaleCompleteTime h v)

lemma CountableRule.admissibleAt_iff_onUnit (π : CountableRule Seed) (B : CountableInstance)
    (ν : Measure Seed) {h : ℝ} (hh : 0 < h) :
    π.AdmissibleAt B ν h ↔ (π.onUnitHorizon h).Admissible B ν := by
  constructor
  · intro hA
    exact hA.mono (fun v hv => (π.firstAcceptance_onUnitHorizon hh v).mp hv)
  · intro hA
    exact hA.mono (fun v hv => (π.firstAcceptance_onUnitHorizon hh v).mpr hv)

noncomputable def CountableRule.individualReachProbabilityAt (π : CountableRule Seed)
    (h : ℝ) (B : CountableInstance) (ν : Measure Seed) (i : ℕ) : ℝ :=
  (B.completeWorldLaw ν).real {v | (scaleCompleteTime h v).2.2.1 i ≤ π.realizedDurationAt h (scaleCompleteTime h v)}

noncomputable def CountableRule.individualSelectionProbabilityAt (π : CountableRule Seed)
    (h : ℝ) (B : CountableInstance) (ν : Measure Seed) (i : ℕ) : ℝ :=
  (B.completeWorldLaw ν).real {v | π.SelectsIndividualAt h (scaleCompleteTime h v) i}

noncomputable def CountableRule.expectedDurationAt (π : CountableRule Seed)
    (h : ℝ) (B : CountableInstance) (ν : Measure Seed) : ℝ :=
  ∫ v, π.realizedDurationAt h (scaleCompleteTime h v) ∂B.completeWorldLaw ν

lemma CountableRule.individualReachProbabilityAt_eq (π : CountableRule Seed) (B : CountableInstance)
    (ν : Measure Seed) {h : ℝ} (hh : 0 < h) (i : ℕ) :
    π.individualReachProbabilityAt h B ν i=(π.onUnitHorizon h).individualReachProbability B ν i := by
  unfold CountableRule.individualReachProbabilityAt CountableRule.individualReachProbability
  congr 1
  ext v
  exact π.reachesIndividualAt_scale hh v i

lemma CountableRule.individualSelectionProbabilityAt_eq (π : CountableRule Seed) (B : CountableInstance)
    (ν : Measure Seed) {h : ℝ} (hh : 0 < h) (i : ℕ) :
    π.individualSelectionProbabilityAt h B ν i=(π.onUnitHorizon h).individualSelectionProbability B ν i := by
  unfold CountableRule.individualSelectionProbabilityAt CountableRule.individualSelectionProbability
  congr 1
  ext v
  exact π.selectsIndividualAt_scale hh v i

lemma CountableRule.expectedDurationAt_eq (π : CountableRule Seed) (B : CountableInstance)
    (ν : Measure Seed) {h : ℝ} (hh : 0 < h) :
    π.expectedDurationAt h B ν=h*(∫ v, (π.onUnitHorizon h).realizedDuration v ∂B.completeWorldLaw ν) := by
  unfold CountableRule.expectedDurationAt
  calc
    _ = ∫ v, h*(π.onUnitHorizon h).realizedDuration v ∂B.completeWorldLaw ν :=
      integral_congr_ae (Eventually.of_forall (π.durationAt_scale hh))
    _ = _ := integral_const_mul _ _

lemma CountableRule.normalized_expectedDurationAt_eq (π : CountableRule Seed) (B : CountableInstance)
    (ν : Measure Seed) {h : ℝ} (hh : 0 < h) :
    π.expectedDurationAt h B ν/h=∫ v, (π.onUnitHorizon h).realizedDuration v ∂B.completeWorldLaw ν := by
  rw [π.expectedDurationAt_eq B ν hh]
  exact mul_div_cancel_left₀ _ hh.ne'

/-- The physical duration is measured from the state's start. The quantity
compared with reach is its expectation divided by the positive horizon. -/
theorem CountableRule.individualReachProbabilityAt_le_twice_normalizedDuration
    (π : CountableRule Seed) (hπ : π.IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {h : ℝ} (hh : 0 < h)
    (hA : π.AdmissibleAt B ν h) (i : ℕ) :
    π.individualReachProbabilityAt h B ν i ≤ 2*(π.expectedDurationAt h B ν/h) := by
  rw [π.individualReachProbabilityAt_eq B ν hh,π.normalized_expectedDurationAt_eq B ν hh]
  exact (π.onUnitHorizon h).individualReachProbability_le_twice_meanDuration
    (π.onUnitHorizon_isMeasurable hπ h) B ν ((π.admissibleAt_iff_onUnit B ν hh).mp hA) i

omit [MeasurableSpace Seed] in
lemma unseenMask_scaleIndividualHistory (h : ℝ) (H : IndividualHistory) :
    unseenMask (scaleIndividualHistory h H)=unseenMask H := by
  funext i
  cases hi : H i <;> simp only [unseenMask,scaleIndividualHistory,Model.scaleObservation,hi,
    Option.map_none,Option.map_some,reduceCtorEq,decide_false,decide_true]

omit [MeasurableSpace Seed] in
lemma countableMarkovRule_onUnitHorizon
    (accept : Seed → IndividualMask → ℝ → Option ℕ → ℝ → Bool) (h : ℝ) :
    (countableMarkovRule accept).onUnitHorizon h=
      countableMarkovRule (fun r A t i x => accept r A (h*t) i x) := by
  unfold CountableRule.onUnitHorizon countableMarkovRule
  congr 1
  · funext r t i x H M
    dsimp only
    rw [unseenMask_scaleIndividualHistory]
  · funext r t x H M
    dsimp only
    rw [unseenMask_scaleIndividualHistory]

omit [MeasurableSpace Seed] in
lemma countableThresholdRule_onUnitHorizon (θ : Seed → IndividualMask → ℝ → Option ℕ → ℝ) (h : ℝ) :
    (countableThresholdRule θ).onUnitHorizon h=countableThresholdRule (fun r A t i => θ r A (h*t) i) :=
  countableMarkovRule_onUnitHorizon _ h

def MonotoneCountableThresholdsAt (h : ℝ) (θ : Seed → IndividualMask → ℝ → Option ℕ → ℝ) : Prop :=
  ∀ r t, t ∈ Icc (0 : ℝ) h →
    (∀ i A D, A i=true → MaskLe A D → θ r A t (some i) ≤ θ r D t (some i)) ∧
    (∀ A D, MaskLe A D → θ r A t none ≤ θ r D t none)

omit [MeasurableSpace Seed] in
lemma monotoneCountableThresholds_onUnit {h : ℝ} (hh : 0 < h)
    (θ : Seed → IndividualMask → ℝ → Option ℕ → ℝ) (hθ : MonotoneCountableThresholdsAt h θ) :
    MonotoneCountableThresholds (fun r A t i => θ r A (h*t) i) := by
  intro r t ht
  exact hθ r (h*t) ((scaleClock_mem_Icc_iff hh t).mpr ht)

theorem countableThresholdRule_strict_reachAt
    (θ : Seed → IndividualMask → ℝ → Option ℕ → ℝ) {h : ℝ} (hh : 0 < h)
    (hθ : MonotoneCountableThresholdsAt h θ) (hπ : (countableThresholdRule θ).IsMeasurable)
    (B : CountableInstance) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hA : (countableThresholdRule θ).AdmissibleAt B ν h) (i : ℕ) :
    (countableThresholdRule θ).individualReachProbabilityAt h B ν i-
      (countableThresholdRule θ).expectedDurationAt h B ν/h ≥
      ((countableThresholdRule θ).individualSelectionProbabilityAt h B ν i)^2/2 := by
  have hM := (countableThresholdRule θ).onUnitHorizon_isMeasurable hπ h
  have hAdm := ((countableThresholdRule θ).admissibleAt_iff_onUnit B ν hh).mp hA
  rw [countableThresholdRule_onUnitHorizon] at hM hAdm
  rw [(countableThresholdRule θ).individualReachProbabilityAt_eq B ν hh,
    (countableThresholdRule θ).individualSelectionProbabilityAt_eq B ν hh,
    (countableThresholdRule θ).normalized_expectedDurationAt_eq B ν hh,countableThresholdRule_onUnitHorizon]
  exact countableThresholdRule_strict_reach _ (monotoneCountableThresholds_onUnit hh θ hθ) hM B ν hAdm i

end ProphetSecretary.Limiting.CountableInstance
