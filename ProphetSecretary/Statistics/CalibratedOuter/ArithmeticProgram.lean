import ProphetSecretary.Statistics.ArithmeticCalibrationAgreement
import ProphetSecretary.Statistics.CalibratedOuter.ArithmeticExecution
import ProphetSecretary.Statistics.CalibratedOuter.ArithmeticWork

/-!
# The counted arithmetic outer program

The outer stage and bounded preparation each run once. The online callback
uses the two stored preparations, the independent online seeds, and only
the current observation and history.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} [NeZero m]

noncomputable def arithmeticLearnerForScales (J : ℕ) (target threshold : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) : Learner n (2*m) :=
  learnerCore (J := J) mu zlo zhi
    (calibrationPlannerSeedLaw n m target.accuracy target.failure target.failure_mem)
    (calibrationPlannerSeedLaw n m threshold.accuracy threshold.failure threshold.failure_mem)
    (calibrationTargetCall target.accuracy target.failure target.failure_mem)
    (calibrationPlannerCall threshold.accuracy threshold.failure threshold.failure_mem)
    (measurable_calibrationTargetCall target.accuracy target.failure target.failure_mem)
    (measurable_calibrationPlannerCall threshold.accuracy threshold.failure threshold.failure_mem)

structure ArithmeticOuterPreparation (n m J : ℕ) (threshold : ArithmeticCalibrationScale) where
  transform : CountedOuterPreparation ℝ n m
  calibration : Option (PreparedArithmeticCalibration n m J ×
    PolicyQueryArray n J (ArithmeticCalibrationBank n m threshold))
  work : ℕ

noncomputable def prepareArithmeticOuter (J : ℕ) (hm : 1≤m)
    (target threshold : ArithmeticCalibrationScale) (mu zlo zhi : ℝ)
    (p : OuterLearnerInput m (arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi)) :
    ArithmeticOuterPreparation n m J threshold :=
  let L := arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi
  let out := preparedOuterInput m hm L p
  if out.pilot=0 then ⟨out,none,out.work+3⟩
  else
    let seed := outerInnerPolicySeed m L p
    let d := calibratedExperiment (out.displayed,seed)
    let banks : CalibrationQueryArrays n m J (ArithmeticCalibrationBank n m target)
        (ArithmeticCalibrationBank n m threshold) := (d.1.2,(fun a => (d.2.1 a).2.2),d.2.2.1)
    let prep := countedArithmeticPrepare target threshold mu zlo zhi
      (reservoirCoordinates.symm d.1.1) (fun a => (d.2.1 a).1)
      (fun a => (d.2.1 a).2.1) banks d.2.2.2
    ⟨out,some (prep,banks.2.2),out.work+prep.work+3⟩

noncomputable def decideArithmeticOuter (threshold : ArithmeticCalibrationScale)
    (p : ArithmeticOuterPreparation n m J threshold) (tags : Fin n → ℝ)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) : Bool × ℕ :=
  countedOuterOnline p.transform tags
    (fun s j y H' => p.calibration.elim (false,0)
      (fun a => countedArithmeticDecision threshold a.1 s y H' j a.2))
    t i x H

def outerPreparationWorkBound (n m : ℕ) : ℕ :=
  10*(m+1)*(n+1)+20*(outerPilotRounds m+1)^2*(n+1)+5+n*(2*m)*(4*m+21)

theorem prepareArithmeticOuter_work (J : ℕ) (hm : 1≤m) (target threshold : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ)
    (p : OuterLearnerInput m (arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi)) :
    (prepareArithmeticOuter J hm target threshold mu zlo zhi p).work ≤
      outerPreparationWorkBound n m+arithmeticCalibrationPreparationBound n m J
        (arithmeticCalibrationCallBound n m target) (arithmeticCalibrationCallBound n m threshold)+3 := by
  let L := arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi
  let out := preparedOuterInput m hm L p
  have hOut : out.work≤outerPreparationWorkBound n m := by
    unfold out preparedOuterInput outerPreparationWorkBound
    exact countedOuterPrepare_work hm _ _ _
  unfold prepareArithmeticOuter
  dsimp only
  split_ifs
  · change out.work+3≤_
    omega
  · dsimp only
    have h := countedArithmeticPrepare_work target threshold mu zlo zhi
      (reservoirCoordinates.symm (calibratedExperiment (out.displayed,outerInnerPolicySeed m L p)).1.1)
      (fun a => ((calibratedExperiment (out.displayed,outerInnerPolicySeed m L p)).2.1 a).1)
      (fun a => ((calibratedExperiment (out.displayed,outerInnerPolicySeed m L p)).2.1 a).2.1)
      ((calibratedExperiment (out.displayed,outerInnerPolicySeed m L p)).1.2,
        (fun a => ((calibratedExperiment (out.displayed,outerInnerPolicySeed m L p)).2.1 a).2.2),
        (calibratedExperiment (out.displayed,outerInnerPolicySeed m L p)).2.2.1)
      (calibratedExperiment (out.displayed,outerInnerPolicySeed m L p)).2.2.2
    apply Nat.add_le_add_right (Nat.add_le_add hOut h)

theorem decideArithmeticOuter_work (J : ℕ) (hm : 1≤m) (target threshold : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ)
    (p : OuterLearnerInput m (arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi))
    (tags : Fin n → ℝ) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (decideArithmeticOuter threshold (prepareArithmeticOuter J hm target threshold mu zlo zhi p)
      tags t i x H).2 ≤ arithmeticCalibrationArrivalBound n m J
        (arithmeticCalibrationCallBound n m threshold)+(n+1)*(4*m+24)+9 := by
  apply countedOuterOnline_work
  intro y H'
  unfold prepareArithmeticOuter
  dsimp only
  split_ifs
  · exact Nat.zero_le _
  · exact countedArithmeticDecision_work target threshold mu zlo zhi _ _ _ _ _ t y H' i

/-- The work bound holds for any subset of arrivals reached by the actual
program; no distributional or confidence event is used. -/
theorem arithmeticOuterDecisionWork (J : ℕ) (hm : 1≤m) (target threshold : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ)
    (p : OuterLearnerInput m (arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi))
    (tags : Fin n → ℝ) (S : Finset (Fin n)) (t x : Fin n → ℝ) (H : Fin n → History n) :
    let prep := prepareArithmeticOuter J hm target threshold mu zlo zhi p
    prep.work+∑ i ∈ S, (decideArithmeticOuter threshold prep tags (t i) i (x i) (H i)).2 ≤
      outerPreparationWorkBound n m+3+n*((n+1)*(4*m+24)+9)+
        (arithmeticCalibrationPreparationBound n m J (arithmeticCalibrationCallBound n m target)
          (arithmeticCalibrationCallBound n m threshold)+
          n*arithmeticCalibrationArrivalBound n m J (arithmeticCalibrationCallBound n m threshold)) := by
  dsimp only
  let W := arithmeticCalibrationArrivalBound n m J (arithmeticCalibrationCallBound n m threshold)
  have hPrep := prepareArithmeticOuter_work J hm target threshold mu zlo zhi p
  have hOnline : (∑ i ∈ S, (decideArithmeticOuter threshold
      (prepareArithmeticOuter J hm target threshold mu zlo zhi p) tags (t i) i (x i) (H i)).2)≤
      n*(W+(n+1)*(4*m+24)+9) := by
    calc
      _ ≤ ∑ _i ∈ S, (W+(n+1)*(4*m+24)+9) :=
        Finset.sum_le_sum (fun i _ => decideArithmeticOuter_work J hm target threshold mu zlo zhi
          p tags (t i) i (x i) (H i))
      _ = S.card*(W+(n+1)*(4*m+24)+9) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ (S.card_le_univ.trans_eq (Fintype.card_fin n))
  refine (Nat.add_le_add hPrep hOnline).trans_eq ?_
  change _ = outerPreparationWorkBound n m+3+n*((n+1)*(4*m+24)+9)+
    (arithmeticCalibrationPreparationBound n m J (arithmeticCalibrationCallBound n m target)
      (arithmeticCalibrationCallBound n m threshold)+n*W)
  ring

omit [NeZero m] in
private lemma countedOuterOnline_value_congr (q : CountedOuterPreparation ℝ n m)
    (tags : Fin n → ℝ) (F G : ℝ → Fin n → ℝ → History n → Bool × ℕ)
    (h : ∀ t i x H, (F t i x H).1=(G t i x H).1)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (countedOuterOnline q tags F t i x H).1=(countedOuterOnline q tags G t i x H).1 := by
  unfold countedOuterOnline
  split_ifs
  · rfl
  · exact h _ _ _ _

/-- The counted outer execution realizes the measured learner on every
validation clock profile with distinct clocks in ([0,1)). The hard work
bound above also covers raw outcomes outside this event. -/
theorem decideArithmeticOuter_eq_outerPolicy (J : ℕ) (hm : 1≤m)
    (target threshold : ArithmeticCalibrationScale) (mu zlo zhi : ℝ)
    (p : OuterLearnerInput m (arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi))
    (hDistinct : ∀ a : Fin m, Function.Injective ((outerInnerPolicySeed m _ p).2.1 a).1)
    (hUnit : ∀ (a : Fin m) (i : Fin n), ((outerInnerPolicySeed m _ p).2.1 a).1 i∈Ico (0 : ℝ) 1)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    let L := arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi
    (decideArithmeticOuter threshold (prepareArithmeticOuter J hm target threshold mu zlo zhi p)
      (outerOnlineTags m L p) t i x H).1=(outerPolicy m hm L).decide p t i x H := by
  dsimp only
  let L := arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi
  let q := preparedOuterInput m hm L p
  let seed := outerInnerPolicySeed m L p
  let tags := outerOnlineTags m L p
  let d := calibratedExperiment (q.displayed,seed)
  let banks : CalibrationQueryArrays n m J (ArithmeticCalibrationBank n m target)
      (ArithmeticCalibrationBank n m threshold) := (d.1.2,(fun a => (d.2.1 a).2.2),d.2.2.1)
  let X := fun a : Fin m => (d.2.1 a).1
  let U := fun a : Fin m => (d.2.1 a).2.1
  let R := countedArithmeticPrepare target threshold mu zlo zhi (reservoirCoordinates.symm d.1.1)
    X U banks d.2.2.2
  let F := fun (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) =>
    countedArithmeticDecision threshold R t x H i banks.2.2
  let G := fun (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) =>
    (L.policy.decide (q.displayed,seed) t i x H,0)
  have hDec : ∀ t i x H, (F t i x H).1=(G t i x H).1 := by
    intro t i x H
    have h := countedArithmeticDecision_eq_measured target threshold mu zlo zhi
      (reservoirCoordinates.symm d.1.1) X U banks hDistinct hUnit d.2.2.2 t x H i
    change (F t i x H).1=_
    refine h.trans ?_
    have hg := learnerCore_decide (J := J) mu zlo zhi
      (calibrationPlannerSeedLaw n m target.accuracy target.failure target.failure_mem)
      (calibrationPlannerSeedLaw n m threshold.accuracy threshold.failure threshold.failure_mem)
      (calibrationTargetCall target.accuracy target.failure target.failure_mem)
      (calibrationPlannerCall threshold.accuracy threshold.failure threshold.failure_mem)
      (measurable_calibrationTargetCall target.accuracy target.failure target.failure_mem)
      (measurable_calibrationPlannerCall threshold.accuracy threshold.failure threshold.failure_mem)
      q.displayed seed t i x H
    exact hg.symm
  have hEq := decidePreparedOuter_eq m hm L p t i x H
  have hQ := countedOuterOnline_value q L seed tags (fun _ _ _ _ => 0) t i x H
  unfold decideArithmeticOuter prepareArithmeticOuter
  dsimp only
  by_cases hp : q.pilot=0
  · change (countedOuterOnline (if q.pilot=0 then _ else _ : ArithmeticOuterPreparation n m J threshold).transform
      tags _ t i x H).1 = _
    rw [if_pos hp]
    exact (by
      change (countedOuterOnline q tags (fun _ _ _ _ => (false,0)) t i x H).1 = _
      simpa only [countedOuterOnline,if_pos hp] using hQ.trans hEq)
  · change (countedOuterOnline (if q.pilot=0 then _ else _ : ArithmeticOuterPreparation n m J threshold).transform
      tags _ t i x H).1 = _
    rw [if_neg hp]
    exact (countedOuterOnline_value_congr q tags F G hDec t i x H).trans (hQ.trans hEq)

theorem decideArithmeticOuter_ae (J : ℕ) (hm : 1≤m) (target threshold : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (P : Instance n) :
    let L := arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi
    ∀ᵐ p ∂outerLearnerInputLaw P m L, ∀ t i x H,
      (decideArithmeticOuter threshold (prepareArithmeticOuter J hm target threshold mu zlo zhi p)
        (outerOnlineTags m L p) t i x H).1=(outerPolicy m hm L).decide p t i x H := by
  dsimp only
  let L := arithmeticLearnerForScales (n := n) (m := m) J target threshold mu zlo zhi
  let E := ArithmeticCalibrationBank n m threshold
  letI : MeasurableSpace E := inferInstanceAs
    (MeasurableSpace (CalibrationPlannerSeed n m threshold.accuracy threshold.failure threshold.failure_mem))
  let A := ValidationAux n m J E
  letI : MeasurableSpace A := by dsimp only [A,ValidationAux,PolicyQueryArray]; infer_instance
  let ν : Measure E := calibrationPlannerSeedLaw n m threshold.accuracy threshold.failure threshold.failure_mem
  letI : IsProbabilityMeasure ν := by dsimp only [ν]; infer_instance
  let V : Measure A := validationAuxLaw (n := n) (m := m) (J := J) ν
  letI : IsProbabilityMeasure V := validationAuxLaw_probability ν
  have hSeed : MeasurePreserving (outerInnerPolicySeed m L) (outerLearnerInputLaw P m L) L.seedLaw :=
    measurePreserving_snd.comp (measurePreserving_snd.comp
      (measurePreserving_snd.comp (measurePreserving_snd.comp measurePreserving_snd)))
  have hAux : MeasurePreserving
      (fun r : L.Seed => (r.2.1 : A)) L.seedLaw V := by
    let O := (policyQueryArrayLaw (n := n) (J := J) ν).prod Instance.uniformClock
    letI : IsProbabilityMeasure O := by dsimp only [O]; infer_instance
    let νT := calibrationPlannerSeedLaw n m target.accuracy target.failure target.failure_mem
    letI : IsProbabilityMeasure νT := by dsimp only [νT]; infer_instance
    exact (measurePreserving_fst (μ := V) (ν := O)).comp
      (measurePreserving_snd (μ := targetQueryArrayLaw νT) (ν := V.prod O))
  have hProfile (a : Fin m) :
      MeasurePreserving (fun q : A => (q a).1)
        V (Instance.clocksLaw n) :=
    measurePreserving_fst.comp (measurePreserving_eval (fun _ : Fin m =>
      (Instance.clocksLaw n).prod (policyQueryArrayLaw ν)) a)
  have hU : ∀ᵐ u ∂Instance.clocksLaw n, ∀ i, u i∈Ico (0 : ℝ) 1 := by
    apply ae_all_iff.mpr
    intro i
    have he := (measurePreserving_eval (fun _ : Fin n => Instance.uniformClock) i).quasiMeasurePreserving
    have h0 : ∀ᵐ t ∂Instance.uniformClock, t∈Icc (0 : ℝ) 1 := ae_restrict_mem measurableSet_Icc
    filter_upwards [he.ae h0, he.ae (Instance.uniformClock.ae_ne 1)] with u h hu
    exact ⟨h.1,lt_of_le_of_ne h.2 hu⟩
  have hGood : ∀ᵐ p ∂outerLearnerInputLaw P m L, ∀ a : Fin m,
      Function.Injective ((outerInnerPolicySeed m L p).2.1 a).1 ∧
      ∀ i, ((outerInnerPolicySeed m L p).2.1 a).1 i∈Ico (0 : ℝ) 1 := by
    apply ae_all_iff.mpr
    intro a
    have h := (hProfile a).comp (hAux.comp hSeed)
    exact h.quasiMeasurePreserving.ae (Instance.clocks_pairwise_distinct.and hU)
  filter_upwards [hGood] with p hp
  exact decideArithmeticOuter_eq_outerPolicy J hm target threshold mu zlo zhi p
    (fun a => (hp a).1) (fun a => (hp a).2)

end ProphetSecretary.Statistics.Calibration
