import ProphetSecretary.Limiting.OmissionCandidateLifting
import ProphetSecretary.Limiting.CountableTruncationTail
import ProphetSecretary.Limiting.HybridPositivePairs

/-!
# Full countable positive close-pair probability

The exact retained-observer coupling transports every finite-prefix witness
to a genuine finite hybrid pair. Continuity from below includes all individual
identities. Only the actual total tail count above the positive level enters
the bound, including the case of infinite anonymous intensity near zero.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Limiting.CountableInstance

lemma prefixClosePositivePair_probability (B : CountableInstance) (hZero : B.terminal=0)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    (N : ℕ) {b η : ℝ} (hb : 0 < b) (hη : 0 ≤ η) :
    (B.completeWorldLaw ν).real (prefixClosePositivePair N b η) ≤
      2*η*((B.totalTailMass b).toReal^2+(B.totalTailMass b).toReal) := by
  let cut := b/2
  have hCut : (B.terminal : ℝ) < cut := by simpa only [hZero,NNReal.coe_zero] using half_pos hb
  have hCutB : cut < b := by dsimp only [cut]; linarith only [hb]
  have hbB : (B.terminal : ℝ) < b := hCut.trans hCutB
  let C := B.truncation N cut hCut
  let ξ := (ν.prod (B.lowCloudLaw cut)).prod ((B.tailValuesLaw N).prod individualClocksLaw)
  obtain ⟨Γ,hΓ,hNew,hOld,hHist⟩ := exists_omissionExecution_coupling B ν N hCut
  letI : IsProbabilityMeasure Γ := hΓ
  have hN : MeasurePreserving (newExecutionWorld N) Γ (C.law ξ) := hNew
  have hConfig : MeasurePreserving (fun q : OmissionExecutionWorld Seed => q.1.1.1) Γ
      (configurationLaw (B.intensityAbove cut hCut)) :=
    (measurePreserving_fst : MeasurePreserving (Prod.fst : HybridWorld N (OmissionAux Seed) → Configuration)
      (C.law ξ) (configurationLaw C.intensity)).comp hN
  have hSub : ∀ᵐ q ∂Γ, oldExecutionWorld q ∈ prefixClosePositivePair N b η →
      newExecutionWorld N q ∈ hybridClosePositivePair b η := by
    filter_upwards [hHist,hOld.quasiMeasurePreserving.ae (B.present_candidate_times_injective ν),
      hConfig.quasiMeasurePreserving.ae (B.intensityAbove_configuration_marks hCut)] with q hq hClock hHigh
    exact omission_prefix_pair_implies_hybrid_pair B N q hCutB hq.1 hq.2 hHigh hClock
  have hCompare : Γ.real {q | oldExecutionWorld q ∈ prefixClosePositivePair N b η} ≤
      Γ.real {q | newExecutionWorld N q ∈ hybridClosePositivePair b η} :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono_ae hSub)
  have hOldReal := congrArg ENNReal.toReal
    (hOld.measure_preimage (measurableSet_prefixClosePositivePair N b η).nullMeasurableSet)
  have hNewReal := congrArg ENNReal.toReal
    (hN.measure_preimage (measurableSet_hybridClosePositivePair b η).nullMeasurableSet)
  change Γ.real {q | oldExecutionWorld q ∈ prefixClosePositivePair N b η}=
    (B.completeWorldLaw ν).real (prefixClosePositivePair N b η) at hOldReal
  change Γ.real {q | newExecutionWorld N q ∈ hybridClosePositivePair b η}=
    (C.law ξ).real (hybridClosePositivePair b η) at hNewReal
  rw [hOldReal,hNewReal] at hCompare
  have hPair := C.closePositivePair_probability ξ b hη
  have hTail : C.tailCount b ≤ (B.totalTailMass b).toReal := B.truncation_tailCount_le N hCut b hbB
  have hTail0 := C.tailCount_nonnegative b
  have hTotal0 : 0 ≤ (B.totalTailMass b).toReal := ENNReal.toReal_nonneg
  have hSquare : (C.tailCount b)^2 ≤ (B.totalTailMass b).toReal^2 := by
    nlinarith only [mul_nonneg (sub_nonneg.mpr hTail) (add_nonneg hTotal0 hTail0)]
  exact (hCompare.trans hPair).trans
    (mul_le_mul_of_nonneg_left (add_le_add hSquare hTail) (mul_nonneg (by norm_num) hη))

/-- This is the close-pair estimate needed for `cor:selected-occurrence` in
an actual full limiting instance, with every candidate counted after stopping. -/
theorem closePositivePair_probability (B : CountableInstance) (hZero : B.terminal=0)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν]
    {b η : ℝ} (hb : 0 < b) (hη : 0 ≤ η) :
    (B.completeWorldLaw ν).real (closePositivePair b η) ≤
      2*η*((B.totalTailMass b).toReal^2+(B.totalTailMass b).toReal) := by
  have hENN := tendsto_measure_iUnion_atTop (μ := B.completeWorldLaw ν)
    (prefixClosePositivePair_mono (Seed := Seed) b η)
  rw [iUnion_prefixClosePositivePair] at hENN
  have hReal := (ENNReal.tendsto_toReal (measure_ne_top _ _)).comp hENN
  exact le_of_tendsto hReal (Eventually.of_forall (fun N => B.prefixClosePositivePair_probability hZero ν N hb hη))

end ProphetSecretary.Limiting.CountableInstance
