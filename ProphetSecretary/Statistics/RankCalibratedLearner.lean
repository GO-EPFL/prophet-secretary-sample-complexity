import ProphetSecretary.Statistics.ReportedRankPreparation
import ProphetSecretary.Model.RankLearner
import ProphetSecretary.Model.ComputedSampling

/-!
# A rank-based learner with assigned numerical timestamps

Each validation profile has a rank order, assigned times, and a fresh
continuation seed array. The online rule uses only the current rank and
observed rank history, and the independently assigned times for those
ranks. A chosen mixing fraction may be rounded before comparison.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ}

noncomputable def RankLearner.ofComputedSamplePolicy (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (π : RankPolicy (Reservoir n k × Seed) n)
    (hπ : π.IsMeasurable) : RankLearner n k where
  Seed := Seed
  seedLaw := ν
  request := firstAvailableRequest k
  measurable_request := measurable_firstAvailableRequest
  decide r D q i x H := π.decide (decodedReservoir D,r) q i x H
  measurable_decide := by
    let A := (Seed × Transcript n) × (Fin n × (Fin n × (ℝ × RankHistory n)))
    have hd : Measurable (fun z : A => decodedReservoir (k := k) z.1.2) :=
      (measurable_decodedReservoir (n := n) (k := k)).comp (measurable_snd.comp measurable_fst)
    have hr : Measurable (fun z : A => z.1.1) := measurable_fst.comp measurable_fst
    exact hπ.comp ((hd.prodMk hr).prodMk measurable_snd)

lemma RankLearner.ofComputedSamplePolicy_decide (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (π : RankPolicy (Reservoir n k × Seed) n)
    (hπ : π.IsMeasurable) (y : Reservoir n k) (r : Seed)
    (q i : Fin n) (x : ℝ) (H : RankHistory n) :
    (RankLearner.ofComputedSamplePolicy Seed ν π hπ).policy.decide (y,r) q i x H=π.decide (y,r) q i x H := by
  change π.decide (decodedReservoir (trainingTranscript (firstAvailableRequest k) r y),r) q i x H=_
  rw [decodedReservoir_firstAvailable_transcript]

lemma RankLearner.ofComputedSamplePolicy_requests_eq (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (π : RankPolicy (Reservoir n k × Seed) n)
    (hπ : π.IsMeasurable) (y : Reservoir n k) (r : Seed) (i : Fin n) :
    requests (trainingTranscript (RankLearner.ofComputedSamplePolicy Seed ν π hπ).request r y) i=k :=
  train_firstAvailable_full r y (n*k) [] (by simp [WithinBudget]) (by simp) i

end ProphetSecretary.Model

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {TSeed PSeed : Type} [NeZero m]

abbrev RankValidationAux (n J : ℕ) (PSeed : Type) :=
  Equiv.Perm (Fin n) × ((Fin n → ℝ) × PolicyQueryArray n J PSeed)

abbrev RankCalibratedSeed (n m J : ℕ) (TSeed PSeed : Type) :=
  (TargetGrid m → TSeed) × ((Fin m → RankValidationAux n J PSeed) ×
    ((Fin n → ℝ) × (PolicyQueryArray n J PSeed × ℝ)))

variable [MeasurableSpace TSeed] [MeasurableSpace PSeed]

noncomputable def rankValidationAuxLaw (order : Measure (Equiv.Perm (Fin n)))
    (times : Measure (Fin n → ℝ)) (νP : Measure PSeed) : Measure (RankValidationAux n J PSeed) :=
  order.prod (times.prod (policyQueryArrayLaw νP))

instance rankValidationAuxLaw_probability (order : Measure (Equiv.Perm (Fin n)))
    (times : Measure (Fin n → ℝ)) (νP : Measure PSeed)
    [IsProbabilityMeasure order] [IsProbabilityMeasure times] [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (rankValidationAuxLaw (J := J) order times νP) := by
  unfold rankValidationAuxLaw
  infer_instance

noncomputable def rankCalibratedSeedLaw (νT : Measure TSeed) (νP : Measure PSeed)
    (order : Measure (Equiv.Perm (Fin n))) (times : Measure (Fin n → ℝ)) (coin : Measure ℝ) :
    Measure (RankCalibratedSeed n m J TSeed PSeed) :=
  (targetQueryArrayLaw νT).prod
    ((Measure.pi (fun _ : Fin m => rankValidationAuxLaw order times νP)).prod
      (times.prod ((policyQueryArrayLaw νP).prod coin)))

instance rankCalibratedSeedLaw_probability (νT : Measure TSeed) (νP : Measure PSeed)
    (order : Measure (Equiv.Perm (Fin n))) (times : Measure (Fin n → ℝ)) (coin : Measure ℝ)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] [IsProbabilityMeasure order]
    [IsProbabilityMeasure times] [IsProbabilityMeasure coin] :
    IsProbabilityMeasure (rankCalibratedSeedLaw (m := m) (J := J) νT νP order times coin) := by
  unfold rankCalibratedSeedLaw
  infer_instance

omit [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m] in
def rankCalibrationData (p : Reservoir n (2*m) × RankCalibratedSeed n m J TSeed PSeed) :
    FirstInformation n m TSeed × (Fin m → RankValidationProfile n J PSeed) :=
  let d := trainingAndValidation p.1
  ((d.1,p.2.1),fun j => (d.2 j,p.2.2.1 j))

omit [NeZero m] in
lemma measurable_rankCalibrationData :
    Measurable (rankCalibrationData (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed)) := by
  let D := Reservoir n (2*m) × RankCalibratedSeed n m J TSeed PSeed
  have hD : Measurable (fun p : D => trainingAndValidation p.1) :=
    (trainingAndValidation_measurePreserving (m := m) (zeroInstance n)).measurable.comp measurable_fst
  have hA : Measurable (fun p : D => p.2.2.1) := by fun_prop
  exact ((measurable_fst.comp hD).prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_pi_lambda _ (fun j => ((measurable_pi_apply j).comp (measurable_snd.comp hD)).prodMk
      ((measurable_pi_apply j).comp hA)))

def rankCalibrationExperiment (p : Reservoir n (2*m) × RankCalibratedSeed n m J TSeed PSeed) :
    (FirstInformation n m TSeed × (Fin m → RankValidationProfile n J PSeed)) ×
      ((Fin n → ℝ) × OnlineCalibrationSeed n J PSeed) :=
  (rankCalibrationData p,p.2.2.2)

omit [NeZero m] in
lemma rankCalibrationExperiment_measurePreserving (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    (order : Measure (Equiv.Perm (Fin n))) (times : Measure (Fin n → ℝ)) (coin : Measure ℝ)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] [IsProbabilityMeasure order]
    [IsProbabilityMeasure times] [IsProbabilityMeasure coin] :
    MeasurePreserving (rankCalibrationExperiment (m := m) (J := J))
      ((P.reservoirLaw (2*m)).prod (rankCalibratedSeedLaw νT νP order times coin))
      (((firstInformationLaw P νT).prod (Measure.pi (fun _ : Fin m =>
        P.valuesLaw.prod (rankValidationAuxLaw order times νP)))).prod
        (times.prod ((policyQueryArrayLaw (n := n) (J := J) νP).prod coin))) := by
  let A := P.trainingCoordinateLaw m
  let B := Measure.pi (fun _ : Fin m => P.valuesLaw)
  let C := targetQueryArrayLaw (m := m) νT
  let D := Measure.pi (fun _ : Fin m => rankValidationAuxLaw (J := J) order times νP)
  let E := times.prod ((policyQueryArrayLaw (n := n) (J := J) νP).prod coin)
  let W := Measure.pi (fun _ : Fin m => P.valuesLaw.prod (rankValidationAuxLaw (J := J) order times νP))
  have hData := (trainingAndValidation_measurePreserving (m := m) P).prod
    (MeasurePreserving.id (rankCalibratedSeedLaw (n := n) (m := m) (J := J) νT νP order times coin))
  have hShuffle := productPairShuffle_measurePreserving A B C (D.prod E)
  have hAssoc := (MeasurePreserving.id (A.prod C)).prod
    ((measurePreserving_prodAssoc B D E).symm MeasurableEquiv.prodAssoc)
  have hPair := (measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ)
    (RankValidationAux n J PSeed) (Fin m) (fun _ => P.valuesLaw)
    (fun _ => rankValidationAuxLaw order times νP)).symm (MeasurableEquiv.arrowProdEquivProdArrow _ _ _)
  have hJoin := (MeasurePreserving.id (A.prod C)).prod (hPair.prod (MeasurePreserving.id E))
  have hEnd := (measurePreserving_prodAssoc (A.prod C) W E).symm MeasurableEquiv.prodAssoc
  exact hEnd.comp (hJoin.comp (hAssoc.comp (hShuffle.comp hData)))

lemma measurable_rankValidationDuration {Ω : Type*} [MeasurableSpace Ω]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    {q : Ω → Reservoir n m} {p : Ω → RankValidationProfile n J PSeed}
    (hq : Measurable q) (hp : Measurable p) (j : Fin (J+1)) :
    Measurable (fun d => rankValidationDuration zlo zhi estimate (q d) (p d) j) := by
  let π := numericalFamilyPolicy zlo zhi estimate j
  let s := fun d => (p d).2.2.1
  let r := fun d => (s d,q d,(p d).2.2.2)
  let a := fun d => (p d).2.1
  let x := fun d => (p d).1
  have hs : Measurable s := (measurable_fst.comp (measurable_snd.comp measurable_snd)).comp hp
  have hr : Measurable r := hs.prodMk (hq.prodMk
    ((measurable_snd.comp (measurable_snd.comp measurable_snd)).comp hp))
  have ha : Measurable a := (measurable_fst.comp measurable_snd).comp hp
  have hx : ∀ i, Measurable (fun d => x d i) := fun i => (measurable_pi_apply i).comp (measurable_fst.comp hp)
  have hπ := π.clockToRank_measurable (numericalFamilyPolicy_isMeasurable zlo zhi estimate he j)
  change Measurable (fun d => 1-∑ i : Fin n, if π.clockToRank.Selects (r d) (a d) (x d) i
    then 1-s d ((a d).symm i) else 0)
  apply Measurable.const_sub
  apply Finset.measurable_sum
  intro i _
  have hI := (measurable_of_finite (fun p : Equiv.Perm (Fin n) => p.symm i)).comp ha
  have hV := measurable_rank_time_eval.comp (hs.prodMk hI)
  exact Measurable.ite (π.clockToRank.measurableSet_selects hπ hr ha hx i)
    (measurable_const.sub hV) measurable_const

lemma measurable_rankValidationPrepare (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    Measurable (rankValidationPrepare (J := J) mu zlo zhi targetEstimate policyEstimate) := by
  let D := FirstInformation n m TSeed × (Fin m → RankValidationProfile n J PSeed)
  have hq : Measurable (fun d : D => reservoirCoordinates.symm d.1.1) :=
    reservoirCoordinates.symm.measurable.comp (measurable_fst.comp measurable_fst)
  have hρ : Measurable (fun d : D => computedTarget mu targetEstimate d.1.1 d.1.2) :=
    (measurable_computedTarget mu targetEstimate hT).comp measurable_fst
  let τ := fun (d : D) (i : Fin m) (j : Fin (J+1)) =>
    rankValidationDuration zlo zhi policyEstimate (reservoirCoordinates.symm d.1.1) (d.2 i) j
  have hτ (i : Fin m) (j : Fin (J+1)) : Measurable (fun d => τ d i j) :=
    measurable_rankValidationDuration zlo zhi policyEstimate hC hq
      ((measurable_pi_apply i).comp measurable_snd) j
  have hS := measurable_durationVectorSelection hτ hρ
  exact hq.prodMk hS

noncomputable def rankCalibratedSamplePolicy (roundProb : ℝ → ℝ) (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed) :
    RankPolicy (Reservoir n (2*m) × RankCalibratedSeed n m J TSeed PSeed) n where
  decide p k i x H :=
    let a := rankValidationPrepare mu zlo zhi targetEstimate policyEstimate (rankCalibrationData p)
    let r := p.2.2.2
    let j := mixturePolicyIndex J (a.2.1,roundProb a.2.2) r.2.2
    (numericalFamilyPolicy zlo zhi policyEstimate j).clockToRank.decide (r.1,a.1,r.2.1) k i x H

lemma rankCalibratedSamplePolicy_isMeasurable (roundProb : ℝ → ℝ) (hRound : Measurable roundProb)
    (mu zlo zhi : ℝ) (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    (rankCalibratedSamplePolicy (J := J) roundProb mu zlo zhi targetEstimate policyEstimate).IsMeasurable := by
  let Ω := (Reservoir n (2*m) × RankCalibratedSeed n m J TSeed PSeed) ×
    (Fin n × (Fin n × (ℝ × RankHistory n)))
  let E := ((Fin n → ℝ) × (Reservoir n m × PolicyQueryArray n J PSeed)) ×
    (Fin n × (Fin n × (ℝ × RankHistory n)))
  let a := fun d : Ω => rankValidationPrepare mu zlo zhi targetEstimate policyEstimate (rankCalibrationData d.1)
  have hA : Measurable a :=
    (measurable_rankValidationPrepare mu zlo zhi targetEstimate policyEstimate hT hC).comp
      (measurable_rankCalibrationData.comp measurable_fst)
  have hPoint : Measurable (fun d : Ω => ((a d).2.1,roundProb (a d).2.2)) :=
    (measurable_fst.comp (measurable_snd.comp hA)).prodMk
      (hRound.comp (measurable_snd.comp (measurable_snd.comp hA)))
  have hR : Measurable (fun d : Ω => d.1.2.2.2) := by fun_prop
  have hIndex := measurable_mixturePolicyIndex (J := J) hPoint (measurable_snd.comp (measurable_snd.comp hR))
  have hEval : Measurable (fun z : E × Fin (J+1) =>
    (numericalFamilyPolicy zlo zhi policyEstimate z.2).clockToRank.decide z.1.1
      z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2) :=
    measurable_from_prod_countable_left (fun j => (numericalFamilyPolicy zlo zhi policyEstimate j).clockToRank_measurable
      (numericalFamilyPolicy_isMeasurable zlo zhi policyEstimate hC j))
  have hInput : Measurable (fun d : Ω => ((d.1.2.2.2.1,(a d).1,d.1.2.2.2.2.1),d.2)) :=
    ((measurable_fst.comp hR).prodMk ((measurable_fst.comp hA).prodMk
      (measurable_fst.comp (measurable_snd.comp hR)))).prodMk measurable_snd
  have h := hEval.comp (hInput.prodMk hIndex)
  simpa only [RankPolicy.IsMeasurable,rankCalibratedSamplePolicy,Function.comp_def,a] using h

noncomputable def rankCalibratedLearner (νT : Measure TSeed) (νP : Measure PSeed)
    (order : Measure (Equiv.Perm (Fin n))) (times : Measure (Fin n → ℝ)) (coin : Measure ℝ)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] [IsProbabilityMeasure order]
    [IsProbabilityMeasure times] [IsProbabilityMeasure coin]
    (roundProb : ℝ → ℝ) (hRound : Measurable roundProb) (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) : RankLearner n (2*m) :=
  RankLearner.ofComputedSamplePolicy (RankCalibratedSeed n m J TSeed PSeed)
    (rankCalibratedSeedLaw νT νP order times coin)
    (rankCalibratedSamplePolicy roundProb mu zlo zhi targetEstimate policyEstimate)
    (rankCalibratedSamplePolicy_isMeasurable roundProb hRound mu zlo zhi targetEstimate policyEstimate hT hC)

end ProphetSecretary.Statistics.Calibration
