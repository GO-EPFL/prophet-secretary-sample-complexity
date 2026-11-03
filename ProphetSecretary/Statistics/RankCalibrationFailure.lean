import ProphetSecretary.Statistics.RankCalibrationSeedCoupling

/-!
# The error event for the finite validation keys and coin

The permutation error is the union over validation profiles. The mixture
threshold is determined offline; a separately sampled coin contributes at
most one grid cell conditional on each prepared point.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

abbrev RankCoupledData (n m J : ℕ) (TSeed PSeed : Type) :=
  Reservoir n (2*m) × RankCalibrationCoupledSeed n m J TSeed PSeed

def coupledRankOfflineData (order : (Fin n → ℝ) → Equiv.Perm (Fin n))
    (d : CoupledCalibrationOffline n m J TSeed PSeed) :
    FirstInformation n m TSeed × (Fin m → RankValidationProfile n J PSeed) :=
  let a := trainingAndValidation d.1
  ((a.1,d.2.1),fun j => (a.2 j,order (d.2.2 j).1,(d.2.2 j).2))

omit [NeZero m] in
lemma measurable_coupledRankOfflineData {order : (Fin n → ℝ) → Equiv.Perm (Fin n)}
    (hOrder : Measurable order) :
    Measurable (coupledRankOfflineData (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed) order) := by
  let D := CoupledCalibrationOffline n m J TSeed PSeed
  have hD : Measurable (fun p : D => trainingAndValidation p.1) :=
    (trainingAndValidation_measurePreserving (m := m) (zeroInstance n)).measurable.comp measurable_fst
  have hAux : Measurable (fun p : D => p.2.2) := measurable_snd.comp measurable_snd
  have h := ((measurable_fst.comp hD).prodMk (measurable_fst.comp measurable_snd)).prodMk
    (measurable_pi_lambda (fun p : D => fun j : Fin m =>
      ((trainingAndValidation p.1).2 j,order (p.2.2 j).1,(p.2.2 j).2)) (fun j =>
      ((measurable_pi_apply j).comp (measurable_snd.comp hD)).prodMk
        ((hOrder.comp (measurable_fst.comp ((measurable_pi_apply j).comp hAux))).prodMk
          (measurable_snd.comp ((measurable_pi_apply j).comp hAux)))))
  exact h

noncomputable def coupledIdealMixture (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : CoupledCalibrationOffline n m J TSeed PSeed) : ℝ :=
  (rankValidationPrepare mu zlo zhi targetEstimate policyEstimate
    (coupledRankOfflineData Instance.arrivalPermutation d)).2.2

omit [MeasurableSpace TSeed] [MeasurableSpace PSeed] in
lemma coupledIdealMixture_range (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : CoupledCalibrationOffline n m J TSeed PSeed) :
    coupledIdealMixture mu zlo zhi targetEstimate policyEstimate d∈Icc (0 : ℝ) 1 := by
  let a := coupledRankOfflineData Instance.arrivalPermutation d
  have h := computedTarget_range mu targetEstimate a.1.1 a.1.2
  have hp := (durationVectorSelection_bounds (rankValidationDuration zlo zhi policyEstimate
    (reservoirCoordinates.symm a.1.1)) a.2
    (ρ := computedTarget mu targetEstimate a.1.1 a.1.2)
    ⟨(by norm_num : (0 : ℝ)<1/2).trans_le h.1,h.2.trans (by norm_num)⟩).2.2
  exact ⟨hp.1.le,hp.2⟩

lemma measurable_coupledIdealMixture (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    Measurable (coupledIdealMixture (J := J) mu zlo zhi targetEstimate policyEstimate) :=
  (measurable_snd.comp measurable_snd).comp ((measurable_rankValidationPrepare mu zlo zhi
    targetEstimate policyEstimate hT hC).comp (measurable_coupledRankOfflineData Instance.measurable_arrivalPermutation))

def validationOrderFailure {N : ℕ} (hN : 0<N) (p : RankCoupledData n m J TSeed PSeed) : Prop :=
  ∃ j : Fin m, roundedValidationPermutation hN (p.2.2.1 j).1 ≠ Instance.arrivalPermutation (p.2.2.1 j).1

def mixtureGridFailure (N : ℕ) (hN : 0<N) (α c : ℝ) : Prop :=
  decide (c<α) ≠ decide (uniformGridRound N hN c<uniformGridRound N hN α)

omit [NeZero m] in
lemma measurableSet_validationOrderFailure {N : ℕ} (hN : 0<N) :
    MeasurableSet {p : RankCoupledData n m J TSeed PSeed | validationOrderFailure hN p} := by
  unfold validationOrderFailure
  rw [Set.setOf_exists]
  apply MeasurableSet.iUnion
  intro j
  have h : Measurable (fun p : RankCoupledData n m J TSeed PSeed => (p.2.2.1 j).1) := by fun_prop
  exact (measurableSet_eq_fun ((measurable_roundedValidationPermutation n N hN).comp h)
    (Instance.measurable_arrivalPermutation.comp h)).compl

lemma measurableSet_mixtureGridFailure {Ω : Type*} [MeasurableSpace Ω] (N : ℕ) (hN : 0<N)
    {α c : Ω → ℝ} (hα : Measurable α) (hc : Measurable c) :
    MeasurableSet {p | mixtureGridFailure N hN (α p) (c p)} := by
  have hr := measurable_uniformGridRound N hN
  change MeasurableSet {p | decide (c p<α p)≠
    decide (uniformGridRound N hN (c p)<uniformGridRound N hN (α p))}
  apply measurableSet_decide_disagreement _ _
  · exact measurableSet_lt hc hα
  · simpa only [Function.comp_def] using measurableSet_lt (hr.comp hc) (hr.comp hα)

omit [NeZero m] in
lemma validationOrderFailure_probability_le (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times] [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    {N : ℕ} (hN : 0<N) :
    ((P.reservoirLaw (2*m)).prod (rankCalibrationCoupledSeedLaw (m := m) (J := J) νT νP times)).real
      {p | validationOrderFailure hN p}≤(m : ℝ)*((n : ℝ)*((n : ℝ)-1))/(2*(N : ℝ)) := by
  let D := RankCoupledData n m J TSeed PSeed
  let μ := (P.reservoirLaw (2*m)).prod (rankCalibrationCoupledSeedLaw (m := m) (J := J) νT νP times)
  let μK := Measure.pi (fun _ : Fin m => Instance.clocksLaw n)
  let E := {k : Fin m → Fin n → ℝ | ∃ j, roundedValidationPermutation hN (k j) ≠ Instance.arrivalPermutation (k j)}
  have hE : MeasurableSet E := by
    unfold E
    rw [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro j
    exact (measurableSet_eq_fun ((measurable_roundedValidationPermutation n N hN).comp (measurable_pi_apply j))
      (Instance.measurable_arrivalPermutation.comp (measurable_pi_apply j))).compl
  have hMap : MeasurePreserving (fun p : D => fun j => (p.2.2.1 j).1) μ μK :=
    (coupledValidationKeys_measurePreserving (m := m) (J := J) νT νP times).comp measurePreserving_snd
  have h := congrArg ENNReal.toReal (hMap.measure_preimage hE.nullMeasurableSet)
  exact h.trans_le (validationPermutationBatch_mismatch_probability n N m hN)

omit [NeZero m] in
lemma mixtureGridFailure_probability_le (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times] [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (N : ℕ) (hN : 0<N) (α : CoupledCalibrationOffline n m J TSeed PSeed → ℝ)
    (hα : Measurable α) (hRange : ∀ d, α d∈Icc (0 : ℝ) 1) :
    ((P.reservoirLaw (2*m)).prod (rankCalibrationCoupledSeedLaw (m := m) (J := J) νT νP times)).real
      {p | mixtureGridFailure N hN (α (coupledCalibrationOfflineCoin p).1) p.2.2.2.2.2}≤1/(N : ℝ) := by
  let D := CoupledCalibrationOffline n m J TSeed PSeed
  let μ := coupledCalibrationOfflineLaw (m := m) (J := J) P νT νP times
  let C := Instance.uniformClock
  let E := {p : D × ℝ | mixtureGridFailure N hN (α p.1) p.2}
  let F := E.indicator (1 : D × ℝ → ℝ)
  have hE : MeasurableSet E := measurableSet_mixtureGridFailure N hN (hα.comp measurable_fst) measurable_snd
  have hFI : Integrable F (μ.prod C) := (integrable_const (1 : ℝ)).indicator hE
  have hMap := coupledCalibrationOfflineCoin_measurePreserving (m := m) (J := J) P νT νP times
  have hMP := congrArg ENNReal.toReal (hMap.measure_preimage hE.nullMeasurableSet)
  have hB : (μ.prod C).real E≤1/(N : ℝ) := by
    rw [← integral_indicator_one hE]
    change (∫ p,F p ∂μ.prod C)≤_
    rw [integral_prod _ hFI]
    have h := integral_mono hFI.integral_prod_left (integrable_const (1/(N : ℝ))) (fun d => by
      let E' := {c | mixtureGridFailure N hN (α d) c}
      have hE' : MeasurableSet E' := measurableSet_mixtureGridFailure N hN measurable_const measurable_id
      change (∫ c,E'.indicator (1 : ℝ → ℝ) c ∂C)≤1/(N : ℝ)
      rw [integral_indicator_one hE']
      exact roundedMixtureCoin_disagreement_probability N hN (hRange d))
    simpa only [integral_const,probReal_univ,one_smul] using h
  exact hMP.trans_le hB

end ProphetSecretary.Statistics.Calibration
