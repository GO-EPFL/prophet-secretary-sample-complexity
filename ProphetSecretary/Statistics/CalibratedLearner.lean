import ProphetSecretary.Statistics.CalibratedValidationSelection
import ProphetSecretary.Statistics.CalibratedTargetCalls
import ProphetSecretary.Model.ComputedSampling

/-!
# The actual two-block calibrated learner

Preparation uses only the completed training transcript and independent
offline randomness. It is computed once before online arrivals. Online
execution receives the prepared empirical block and selected mixture, a fresh
query array, the independent mixture coin, and the current causal history.
The full-sample request scan and all cap/zero decisions hold on every input.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type}

abbrev PreparedCalibration (n m : ℕ) := Reservoir n m × (ℕ × ℝ)

def lowerPolicyIndex (J segment : ℕ) : Fin (J+1) := ⟨min (segment-2) J,by omega⟩
def upperPolicyIndex (J segment : ℕ) : Fin (J+1) := ⟨min (segment-1) J,by omega⟩

noncomputable def mixturePolicyIndex (J : ℕ) (point : ℕ × ℝ) (coin : ℝ) : Fin (J+1) :=
  if coin < point.2 then upperPolicyIndex J point.1 else lowerPolicyIndex J point.1

noncomputable def prepare [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) : PreparedCalibration n m :=
  let data := calibratedExperiment p
  let q := reservoirCoordinates.symm data.1.1
  let rho := computedTarget mu targetEstimate data.1.1 data.1.2
  (q,validationSelection zlo zhi policyEstimate q data.2.1 rho)

noncomputable def decidePrepared [NeZero m] (zlo zhi : ℝ)
    (policyEstimate : ContinuationEstimator n m PSeed) (p : PreparedCalibration n m)
    (r : PolicyQueryArray n J PSeed) (coin t : ℝ) (i : Fin n) (x : ℝ) (H : History n) : Bool :=
  (numericalFamilyPolicy zlo zhi policyEstimate (mixturePolicyIndex J p.2 coin)).decide (p.1,r) t i x H

noncomputable def samplePolicy [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed) :
    Policy (Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) n where
  decide p t i x H := decidePrepared zlo zhi policyEstimate (prepare mu zlo zhi targetEstimate policyEstimate p)
    p.2.2.2.1 p.2.2.2.2 t i x H

lemma measurable_mixturePolicyIndex {Ω : Type*} [MeasurableSpace Ω]
    {point : Ω → ℕ × ℝ} {coin : Ω → ℝ} (hp : Measurable point) (hc : Measurable coin) :
    Measurable (fun p => mixturePolicyIndex J (point p) (coin p)) :=
  Measurable.ite (measurableSet_lt hc (measurable_snd.comp hp))
    ((measurable_of_countable (upperPolicyIndex J)).comp (measurable_fst.comp hp))
    ((measurable_of_countable (lowerPolicyIndex J)).comp (measurable_fst.comp hp))

lemma measurable_prepare [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    Measurable (prepare (J := J) mu zlo zhi targetEstimate policyEstimate) := by
  let Ω := Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed
  have hData : Measurable (calibratedExperiment (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed)) :=
    (calibratedExperiment_measurePreserving (zeroInstance n) νT νP).measurable
  have hInfo := measurable_fst.comp hData
  have hQ : Measurable (fun p : Ω => reservoirCoordinates.symm (calibratedExperiment p).1.1) :=
    reservoirCoordinates.symm.measurable.comp (measurable_fst.comp hInfo)
  have hW := measurable_fst.comp (measurable_snd.comp hData)
  have hRho := (measurable_computedTarget mu targetEstimate hT).comp hInfo
  exact hQ.prodMk (measurable_validationSelection zlo zhi policyEstimate hC hQ hW hRho)

lemma samplePolicy_isMeasurable [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    (samplePolicy (J := J) mu zlo zhi targetEstimate policyEstimate).IsMeasurable := by
  let Ω := (Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) × (ℝ × (Fin n × (ℝ × History n)))
  let E := (Reservoir n m × PolicyQueryArray n J PSeed) × (ℝ × (Fin n × (ℝ × History n)))
  have hPrep : Measurable (fun q : Ω => prepare (J := J) mu zlo zhi targetEstimate policyEstimate q.1) :=
    (measurable_prepare (J := J) mu zlo zhi targetEstimate policyEstimate hT hC νT νP).comp measurable_fst
  have hQ := measurable_fst.comp hPrep
  have hPoint := measurable_snd.comp hPrep
  have hOnline : Measurable (fun q : Ω => q.1.2.2.2.1) := by fun_prop
  have hCoin : Measurable (fun q : Ω => q.1.2.2.2.2) := by fun_prop
  have hIndex := measurable_mixturePolicyIndex (J := J) hPoint hCoin
  have hEval : Measurable (fun p : E × Fin (J+1) =>
      (numericalFamilyPolicy zlo zhi policyEstimate p.2).decide p.1.1 p.1.2.1 p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2) :=
    measurable_from_prod_countable_left (fun j => numericalFamilyPolicy_isMeasurable zlo zhi policyEstimate hC j)
  change Measurable (fun q : Ω => (numericalFamilyPolicy zlo zhi policyEstimate
    (mixturePolicyIndex J (prepare (J := J) mu zlo zhi targetEstimate policyEstimate q.1).2 q.1.2.2.2.2)).decide
      ((prepare (J := J) mu zlo zhi targetEstimate policyEstimate q.1).1,q.1.2.2.2.1)
      q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2)
  have hFinal := hEval.comp (((hQ.prodMk hOnline).prodMk measurable_snd).prodMk hIndex)
  simpa only [Function.comp_def] using hFinal

@[simp] lemma samplePolicy_accepts_cap [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) (t : ℝ) (i : Fin n) (H : History n) :
    (samplePolicy mu zlo zhi targetEstimate policyEstimate).decide p t i 1 H=true := by
  simp [samplePolicy,decidePrepared]

@[simp] lemma samplePolicy_rejects_zero [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) (t : ℝ) (i : Fin n) (H : History n) :
    (samplePolicy mu zlo zhi targetEstimate policyEstimate).decide p t i 0 H=false := by
  simp [samplePolicy,decidePrepared]

/-- The causal learner requests exactly `2m` samples from every distribution. -/
noncomputable def learnerCore [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m] (mu zlo zhi : ℝ)
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) : Learner n (2*m) :=
  Learner.ofComputedSamplePolicy (CalibratedSeed n m J TSeed PSeed) (calibratedSeedLaw (n := n) (m := m) (J := J) νT νP)
    (samplePolicy (J := J) mu zlo zhi targetEstimate policyEstimate)
    (samplePolicy_isMeasurable (J := J) mu zlo zhi targetEstimate policyEstimate hT hC νT νP)

lemma learnerCore_requests_eq [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m] (mu zlo zhi : ℝ)
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (y : Reservoir n (2*m)) (r : CalibratedSeed n m J TSeed PSeed) (i : Fin n) :
    requests (trainingTranscript (learnerCore (J := J) mu zlo zhi νT νP targetEstimate policyEstimate hT hC).request r y) i=2*m :=
  Learner.ofComputedSamplePolicy_requests_eq _ _ _ _ y r i

lemma learnerCore_decide [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m] (mu zlo zhi : ℝ)
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (y : Reservoir n (2*m)) (r : CalibratedSeed n m J TSeed PSeed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (learnerCore (J := J) mu zlo zhi νT νP targetEstimate policyEstimate hT hC).policy.decide (y,r) t i x H =
      (samplePolicy mu zlo zhi targetEstimate policyEstimate).decide (y,r) t i x H :=
  Learner.ofComputedSamplePolicy_decide _ _ _ _ y r t i x H

/-- Public empty-size and small-budget branches use no confidence search or sample request. -/
noncomputable def degenerateLearner (n m : ℕ) : Learner n (2*m) where
  Seed := Unit
  seedLaw := Measure.dirac ()
  request _ _ := none
  measurable_request := measurable_const
  decide _ _ _ _ x _ := if x=1 then true else false
  measurable_decide := measurable_const.ite
    (measurableSet_eq_fun (by fun_prop) measurable_const) measurable_const

lemma degenerateLearner_requests_eq_zero (n m : ℕ) (y : Reservoir n (2*m)) (r : Unit) (i : Fin n) :
    requests (trainingTranscript (degenerateLearner n m).request r y) i=0 := by
  unfold trainingTranscript
  cases n*(2*m) <;> rfl

@[simp] lemma degenerateLearner_accepts_cap (n m : ℕ) (y : Reservoir n (2*m)) (r : Unit)
    (t : ℝ) (i : Fin n) (H : History n) :
    (degenerateLearner n m).policy.decide (y,r) t i 1 H=true := by simp [Learner.policy,degenerateLearner]

@[simp] lemma degenerateLearner_rejects_zero (n m : ℕ) (y : Reservoir n (2*m)) (r : Unit)
    (t : ℝ) (i : Fin n) (H : History n) :
    (degenerateLearner n m).policy.decide (y,r) t i 0 H=false := by
  change (if (0 : ℝ)=1 then true else false)=false
  norm_num

lemma prepare_selection_bounds [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) :
    1 ≤ (prepare mu zlo zhi targetEstimate policyEstimate p).2.1 ∧
    (prepare mu zlo zhi targetEstimate policyEstimate p).2.1 ≤ J+2 ∧
    (prepare mu zlo zhi targetEstimate policyEstimate p).2.2 ∈ Ioc (0 : ℝ) 1 := by
  let data := calibratedExperiment p
  let q := reservoirCoordinates.symm data.1.1
  let ρ := computedTarget mu targetEstimate data.1.1 data.1.2
  have hr := computedTarget_range mu targetEstimate data.1.1 data.1.2
  have hρ : ρ ∈ Ioc (0 : ℝ) 1 := ⟨by dsimp [ρ]; linarith [hr.1], by dsimp [ρ]; linarith [hr.2]⟩
  exact validationSelection_bounds zlo zhi policyEstimate q data.2.1 hρ

@[simp] lemma mixturePolicyIndex_left (J : ℕ) (α coin : ℝ) :
    mixturePolicyIndex J (1,α) coin = ⟨0,by omega⟩ := by
  unfold mixturePolicyIndex
  split_ifs <;> apply Fin.ext <;> simp [upperPolicyIndex,lowerPolicyIndex]

@[simp] lemma mixturePolicyIndex_right (J : ℕ) (α coin : ℝ) :
    mixturePolicyIndex J (J+2,α) coin = ⟨J,by omega⟩ := by
  unfold mixturePolicyIndex
  split_ifs <;> apply Fin.ext <;> simp [upperPolicyIndex,lowerPolicyIndex]

end ProphetSecretary.Statistics.Calibration
