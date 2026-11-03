import ProphetSecretary.Statistics.RankCalibratedLearner
import ProphetSecretary.Statistics.CalibratedSelectorExecution
import ProphetSecretary.Model.RankOutcomeAgreement
import ProphetSecretary.Model.RankToClockLaw

/-!
# The rank deployment of a prepared mixture

Rounded sorted timestamps and the exogenous permutation have their
independent laws. Conditioning on the prepared offline point, this rank
execution has the same reward and reach as its continuous comparison.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {PSeed : Type} [MeasurableSpace PSeed] [NeZero m]

/-- The law of independently assigned sorted numerical timestamps after applying a measurable clock map. -/
noncomputable def mappedSortedClockLaw (n : ℕ) (f : ℝ → ℝ) (_hf : Measurable f) : Measure (Fin n → ℝ) :=
  (Instance.sortedTimesLaw n).map (fun s i => f (s i))

instance mappedSortedClockLaw_probability (n : ℕ) (f : ℝ → ℝ) (hf : Measurable f) :
    IsProbabilityMeasure (mappedSortedClockLaw n f hf) :=
  Measure.isProbabilityMeasure_map (measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))).aemeasurable

noncomputable def roundedPreparedRankPolicy (νP : Measure PSeed) [IsProbabilityMeasure νP]
    (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (a : PreparedCalibration n m) : RandomizedRankPolicy n where
  Seed := (Fin n → ℝ) × OnlineCalibrationSeed n J PSeed
  seedLaw := times.prod (onlineCalibrationSeedLaw νP)
  rule := (preparedPolicy zlo zhi estimate a).clockToRank
  measurable_rule := (preparedPolicy zlo zhi estimate a).clockToRank_measurable
    (preparedPolicy_isMeasurable zlo zhi estimate he a)

noncomputable def roundedComparisonPolicy (νP : Measure PSeed) [IsProbabilityMeasure νP]
    {f : ℝ → ℝ} (hf : Measurable f) (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
    (a : PreparedCalibration n m) : RandomizedPolicy n :=
  RandomizedPolicy.ofRule (onlineCalibrationSeedLaw (n := n) (J := J) νP)
    (preparedPolicy zlo zhi (clockRoundedEstimate f estimate) a)
    (preparedPolicy_isMeasurable zlo zhi (clockRoundedEstimate f estimate)
      (measurable_clockRoundedEstimate hf estimate he) a)

section

variable (P : Instance n) (νP : Measure PSeed) [IsProbabilityMeasure νP]
  {f : ℝ → ℝ} (hf : Measurable f) {zlo zhi : ℝ} (h0 : 0≤zlo) (hz : zlo≤zhi)
  (hF : ∀ t∈Icc (0 : ℝ) 1, f t∈Icc (0 : ℝ) t)
  (estimate : ContinuationEstimator n m PSeed)
  (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
    estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))
  (a : PreparedCalibration n m)

local notation "N" => onlineCalibrationSeedLaw (n := n) (J := J) νP
local notation "A" => roundedComparisonPolicy (J := J) νP hf zlo zhi estimate he a
local notation "S" => Instance.sortedTimesLaw n

include hf in
private lemma measurable_round_sorted : Measurable (fun s : Fin n → ℝ => fun i => f (s i)) :=
  measurable_pi_lambda _ (fun i => hf.comp (measurable_pi_apply i))

local notation "R" =>
  roundedPreparedRankPolicy (J := J) νP (mappedSortedClockLaw n f hf) zlo zhi estimate he a

private def roundRankDeployment (ω : (A).clockToRank.World) : (R).World :=
  (ω.1,ω.2.1,f ∘ ω.2.2.1,ω.2.2.2)

private lemma roundRankDeployment_measurePreserving :
    MeasurePreserving (roundRankDeployment νP hf estimate he a) ((A).clockToRank.worldLaw P) ((R).worldLaw P) := by
  have hM : MeasurePreserving (fun s : Fin n → ℝ => fun i => f (s i)) S (mappedSortedClockLaw n f hf) :=
    ⟨measurable_round_sorted hf,rfl⟩
  exact (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod
    (hM.prod (MeasurePreserving.id N)))

private lemma roundRankDeployment_ae_clock_unit :
    ∀ᵐ ω : (A).clockToRank.World ∂(A).clockToRank.worldLaw P,
      StrictMono ω.2.2.1 ∧ ∀ i, ω.2.2.1 i∈Icc (0 : ℝ) 1 := by
  have hM := (A).clockToRankWorld_measurePreserving P
  filter_upwards [(A).clockToRank_sortedTimes_regular P,
    hM.quasiMeasurePreserving.ae (P.world_clocks_mem_unitInterval N)] with ω hS hU
  refine ⟨hS.1,fun i => ?_⟩
  have h := hU (ω.2.1 i)
  simpa only [RandomizedPolicy.clockToRankWorld,Instance.reconstructClocks,Equiv.symm_apply_apply] using h

include h0 hz hF in
theorem roundedPreparedRankPolicy_expectedReward_eq (hP : Integrable Instance.maximum P.valuesLaw) :
    (R).expectedReward P=(A).expectedReward P := by
  let L := (A).clockToRank.worldLaw P
  let U := (A).clockToRankWorld
  let V := roundRankDeployment (J := J) νP hf (zlo := zlo) (zhi := zhi) estimate he a
  have h1 := (A).clockToRankWorld_measurePreserving P
  have h2 := roundRankDeployment_measurePreserving (J := J) P νP hf (zlo := zlo) (zhi := zhi) estimate he a
  have hEq : ∀ᵐ ω ∂L, (R).realizedReward (V ω)=(A).realizedReward (U ω) := by
    filter_upwards [roundRankDeployment_ae_clock_unit (J := J) P νP hf (zlo := zlo) (zhi := zhi) estimate he a] with ω hω
    let π := preparedPolicy (J := J) zlo zhi estimate a
    let s := ω.2.2.1
    let p := ω.2.1
    let r := ω.2.2.2
    let u := Instance.reconstructClocks (s,p)
    have h := Policy.outcomes_eq_of_actions_eq (A).rule π.clockToRank.rankToClock r (f ∘ s,r)
      Finset.univ ω.1 u (fun i =>
        (preparedPolicy_clockRounded_action h0 hz f hF estimate a r.1 r.2 s hω.1 hω.2 p ω.1 i).trans
          (π.clockToRank.rankToClock_action (f ∘ s,r) s hω.1 p ω.1 i).symm)
    exact (π.clockToRank.rankToClock_reward (f ∘ s,r) s hω.1 (fun k => (hω.2 k).2) p ω.1).symm.trans h.1.symm
  calc
    _ = ∫ ω,(R).realizedReward (V ω) ∂L :=
      (h2.hasLaw.integral_comp ((R).integrable_realizedReward P hP).aestronglyMeasurable).symm
    _ = ∫ ω,(A).realizedReward (U ω) ∂L := integral_congr_ae hEq
    _ = _ := h1.hasLaw.integral_comp ((A).integrable_realizedReward P hP).aestronglyMeasurable

include h0 hz hF in
theorem roundedPreparedRankPolicy_reachProbability_eq (i : Fin n) :
    (R).reachProbability P i=(A).rule.reachProbability P N i := by
  let L := (A).clockToRank.worldLaw P
  let U := (A).clockToRankWorld
  let V := roundRankDeployment (J := J) νP hf (zlo := zlo) (zhi := zhi) estimate he a
  let E := {ω : (R).World | (R).rule.Reaches ω.2.2 ω.2.1 ω.1 i}
  let F := {ω : (A).World | (A).rule.Reaches ω.2.2 ω.1 ω.2.1 i}
  have hE : MeasurableSet E := (R).rule.measurableSet_reaches (R).measurable_rule
    (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst) i
  have hF' : MeasurableSet F := (A).rule.measurableSet_reaches (A).measurable_rule
    (measurable_snd.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  have h1 := (A).clockToRankWorld_measurePreserving P
  have h2 := roundRankDeployment_measurePreserving (J := J) P νP hf (zlo := zlo) (zhi := zhi) estimate he a
  have hEq : V ⁻¹' E =ᵐ[L] U ⁻¹' F := by
    filter_upwards [roundRankDeployment_ae_clock_unit (J := J) P νP hf (zlo := zlo) (zhi := zhi) estimate he a] with ω hω
    apply propext
    let π := preparedPolicy (J := J) zlo zhi estimate a
    let s := ω.2.2.1
    let p := ω.2.1
    let r := ω.2.2.2
    let u := Instance.reconstructClocks (s,p)
    have h := Policy.outcomes_eq_of_actions_eq (A).rule π.clockToRank.rankToClock r (f ∘ s,r)
      Finset.univ ω.1 u (fun k =>
        (preparedPolicy_clockRounded_action h0 hz f hF estimate a r.1 r.2 s hω.1 hω.2 p ω.1 k).trans
          (π.clockToRank.rankToClock_action (f ∘ s,r) s hω.1 p ω.1 k).symm)
    change π.clockToRank.Reaches (f ∘ s,r) p ω.1 i ↔ (A).rule.Reaches r ω.1 u i
    have hR := π.clockToRank.rankToClock_reaches (f ∘ s,r) s hω.1 (fun k => (hω.2 k).2) p ω.1 i
    rw [← hR,Policy.Reaches,Policy.Reaches,h.2]
  change ((R).worldLaw P).real E=(P.worldLaw N).real F
  calc
    _ = L.real (V ⁻¹' E) := (congrArg ENNReal.toReal (h2.measure_preimage hE.nullMeasurableSet)).symm
    _ = L.real (U ⁻¹' F) := congrArg ENNReal.toReal (measure_congr hEq)
    _ = _ := congrArg ENNReal.toReal (h1.measure_preimage hF'.nullMeasurableSet)

end

end ProphetSecretary.Statistics.Calibration

/-!
# The ideal rounded rank learner has the reported selector's law

The sorted clock grid and uniform permutation specify each independent
validation profile. With a fresh uniform mixture coin, conditioning on
these profiles leaves exactly the prepared rank policy. The distributional
comparison precedes rounding the permutation keys and the mixture coin.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

abbrev RankCalibrationOffline (n m J : ℕ) (TSeed PSeed : Type) :=
  FirstInformation n m TSeed × (Fin m → RankValidationProfile n J PSeed)
abbrev RankCalibrationOnline (n J : ℕ) (PSeed : Type) :=
  (Fin n → ℝ) × OnlineCalibrationSeed n J PSeed

section

variable (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
  [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
  (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times]
  (mu zlo zhi : ℝ) (targetEstimate : TargetEstimator n m TSeed)
  (policyEstimate : ContinuationEstimator n m PSeed)
  (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
  (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
    policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "D" => RankCalibrationOffline n m J TSeed PSeed
local notation "S" => RankCalibrationOnline n J PSeed
local notation "O" => Measure.prod (firstInformationLaw (m := m) P νT) (Measure.pi (fun _ : Fin m =>
    rankValidationProfileLaw (J := J) P νP times))
local notation "N" => Measure.prod times (onlineCalibrationSeedLaw (n := n) (J := J) νP)
local notation "A" => rankValidationPrepare (J := J) mu zlo zhi targetEstimate policyEstimate
local notation "L" => rankCalibratedLearner (J := J) νT νP (Instance.uniformPermutationLaw n)
    times Instance.uniformClock id measurable_id mu zlo zhi targetEstimate policyEstimate hT hC
local notation "C" => fun d : D => roundedPreparedRankPolicy (J := J) νP times zlo zhi policyEstimate hC (A d)

private noncomputable def preparedRankJointRule : RankPolicy (D × S) n where
  decide p k i x H :=
    let a := A p.1
    let r := p.2
    let j := mixturePolicyIndex J a.2 r.2.2
    (numericalFamilyPolicy zlo zhi policyEstimate j).clockToRank.decide (r.1,a.1,r.2.1) k i x H

include hT hC in
private lemma preparedRankJointRule_isMeasurable :
    (preparedRankJointRule (J := J) mu zlo zhi targetEstimate policyEstimate).IsMeasurable := by
  let Ω := (D × S) × (Fin n × (Fin n × (ℝ × RankHistory n)))
  let E := ((Fin n → ℝ) × (Reservoir n m × PolicyQueryArray n J PSeed)) ×
    (Fin n × (Fin n × (ℝ × RankHistory n)))
  have hA : Measurable (fun p : Ω => A p.1.1) :=
    (measurable_rankValidationPrepare mu zlo zhi targetEstimate policyEstimate hT hC).comp
      (measurable_fst.comp measurable_fst)
  have hR : Measurable (fun p : Ω => p.1.2) := measurable_snd.comp measurable_fst
  have hIndex := measurable_mixturePolicyIndex (J := J) (measurable_snd.comp hA)
    (measurable_snd.comp (measurable_snd.comp hR))
  have hEval : Measurable (fun z : E × Fin (J+1) =>
    (numericalFamilyPolicy zlo zhi policyEstimate z.2).clockToRank.decide z.1.1
      z.1.2.1 z.1.2.2.1 z.1.2.2.2.1 z.1.2.2.2.2) :=
    measurable_from_prod_countable_left (fun j => (numericalFamilyPolicy zlo zhi policyEstimate j).clockToRank_measurable
      (numericalFamilyPolicy_isMeasurable zlo zhi policyEstimate hC j))
  have hInput : Measurable (fun d : Ω => ((d.1.2.1,(A d.1.1).1,d.1.2.2.1),d.2)) :=
    ((measurable_fst.comp hR).prodMk ((measurable_fst.comp hA).prodMk
      (measurable_fst.comp (measurable_snd.comp hR)))).prodMk measurable_snd
  have h := hEval.comp (hInput.prodMk hIndex)
  simpa only [RankPolicy.IsMeasurable,preparedRankJointRule,Function.comp_def] using h

private noncomputable def preparedRankJointPolicy : RandomizedRankPolicy n where
  Seed := D × S
  seedLaw := (O).prod N
  rule := preparedRankJointRule mu zlo zhi targetEstimate policyEstimate
  measurable_rule := preparedRankJointRule_isMeasurable (J := J) mu zlo zhi targetEstimate policyEstimate hT hC

local notation "Q" => preparedRankJointPolicy (J := J) P νT νP times mu zlo zhi targetEstimate policyEstimate hT hC

private def jointRankWorld (p : D × ((Fin n → ℝ) × (Equiv.Perm (Fin n) × S))) :
    (Fin n → ℝ) × (Equiv.Perm (Fin n) × (D × S)) :=
  (p.2.1,p.2.2.1,p.1,p.2.2.2)

omit [NeZero m] in
private lemma jointRankWorld_measurePreserving :
    MeasurePreserving (jointRankWorld (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed))
      ((O).prod (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod N)))
      (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ((O).prod N))) := by
  let X := P.valuesLaw
  let U := Instance.uniformPermutationLaw n
  have h1 := (MeasurePreserving.id O).prod ((measurePreserving_prodAssoc X U N).symm MeasurableEquiv.prodAssoc)
  have h2 := (measurePreserving_prodAssoc O (X.prod U) N).symm MeasurableEquiv.prodAssoc
  have h3 := (Measure.measurePreserving_swap (μ := O) (ν := X.prod U)).prod (MeasurePreserving.id N)
  have h4 := measurePreserving_prodAssoc (X.prod U) O N
  have h5 := measurePreserving_prodAssoc X U ((O).prod N)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

private def rawRankWorld
    (ω : (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n (2*m) × RankCalibratedSeed n m J TSeed PSeed))) :
    D × ((Fin n → ℝ) × (Equiv.Perm (Fin n) × S)) :=
  ((rankCalibrationExperiment ω.2.2).1,ω.1,ω.2.1,(rankCalibrationExperiment ω.2.2).2)

omit [NeZero m] in
private lemma rawRankWorld_measurePreserving :
    MeasurePreserving (rawRankWorld (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed))
      (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod
        ((P.reservoirLaw (2*m)).prod (rankCalibratedSeedLaw νT νP
          (Instance.uniformPermutationLaw n) times Instance.uniformClock))))
      ((O).prod (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod N))) := by
  let X := P.valuesLaw
  let U := Instance.uniformPermutationLaw n
  let T := (P.reservoirLaw (2*m)).prod (rankCalibratedSeedLaw (n := n) (m := m) (J := J) νT νP
    U times Instance.uniformClock)
  have h1 := (measurePreserving_prodAssoc X U T).symm MeasurableEquiv.prodAssoc
  have h2 := (MeasurePreserving.id (X.prod U)).prod (rankCalibrationExperiment_measurePreserving
    (m := m) (J := J) P νT νP U times Instance.uniformClock)
  have h3 := (measurePreserving_prodAssoc (X.prod U) O N).symm MeasurableEquiv.prodAssoc
  have h4 := (Measure.measurePreserving_swap (μ := X.prod U) (ν := O)).prod (MeasurePreserving.id N)
  have h5 := measurePreserving_prodAssoc O (X.prod U) N
  have h6 := (MeasurePreserving.id O).prod (measurePreserving_prodAssoc X U N)
  exact h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))

private lemma jointRank_action (d : D) (s : S) (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    (Q).rule.action (d,s) p x i=(C d).rule.action s p x i := by
  change _=(preparedPolicy zlo zhi policyEstimate (A d)).decide s.2 (s.1 (p.symm i)) i (x i)
    (fun j => (rankHistory p x (p.symm i) j).map (fun z => (s.1 z.1,z.2)))
  rw [preparedPolicy_decide]
  rfl

private lemma rawRank_action
    (ω : (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n (2*m) × RankCalibratedSeed n m J TSeed PSeed)))
    (i : Fin n) :
    (L).policy.action ω.2.2 ω.2.1 ω.1 i=
      (Q).rule.action ((rankCalibrationExperiment ω.2.2).1,(rankCalibrationExperiment ω.2.2).2) ω.2.1 ω.1 i := by
  exact RankLearner.ofComputedSamplePolicy_decide _ _ _ _ ω.2.2.1 ω.2.2.2 _ i _ _

theorem idealRankCalibratedLearner_reward_eq_integral (hP : Integrable Instance.maximum P.valuesLaw) :
    (L).expectedReward P=∫ d,(C d).expectedReward P ∂O := by
  have hM := jointRankWorld_measurePreserving (m := m) (J := J) P νT νP times
  have hS := rawRankWorld_measurePreserving (m := m) (J := J) P νT νP times
  have hI := hM.integrable_comp_of_integrable ((Q).integrable_realizedReward P hP)
  have hMap := hS.hasLaw.integral_comp hI.aestronglyMeasurable
  calc
    _ = ∫ ω, (Q).realizedReward (jointRankWorld (rawRankWorld ω))
        ∂((L).randomizedPolicy P).worldLaw P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        RankPolicy.reward_eq_of_actions_eq _ _ _ _ _ _
          (rawRank_action P νT νP times mu zlo zhi targetEstimate policyEstimate hT hC ω)
    _ = ∫ p, ((Q).realizedReward ∘ jointRankWorld) p
        ∂(O).prod (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod N)) := hMap
    _ = (∫ d,∫ w, ((Q).realizedReward ∘ jointRankWorld) (d,w)
        ∂P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod N) ∂O) := integral_prod _ hI
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        RankPolicy.reward_eq_of_actions_eq _ _ _ _ _ _
          (jointRank_action P νT νP times mu zlo zhi targetEstimate policyEstimate hT hC d ω.2.2 ω.2.1 ω.1))

private noncomputable def rankReachValue (π : RandomizedRankPolicy n) (i : Fin n) (ω : π.World) : ℝ :=
  if π.rule.Reaches ω.2.2 ω.2.1 ω.1 i then 1 else 0

private lemma rankReachValue_integrable (π : RandomizedRankPolicy n) (i : Fin n) :
    Integrable (rankReachValue π i) (π.worldLaw P) := by
  have h := π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
    (measurable_fst.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst) i
  exact (integrable_const (1 : ℝ)).indicator h

private lemma rankReachValue_integral (π : RandomizedRankPolicy n) (i : Fin n) :
    (∫ w,rankReachValue π i w ∂π.worldLaw P)=π.reachProbability P i :=
  integral_indicator_one (π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
    (measurable_fst.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst) i)

theorem idealRankCalibratedLearner_reach_eq_integral (i : Fin n) :
    (L).reachProbability P i=∫ d,(C d).reachProbability P i ∂O := by
  let f := rankReachValue Q i
  have hM := jointRankWorld_measurePreserving (m := m) (J := J) P νT νP times
  have hS := rawRankWorld_measurePreserving (m := m) (J := J) P νT νP times
  have hI := hM.integrable_comp_of_integrable (rankReachValue_integrable P Q i)
  have hMap := hS.hasLaw.integral_comp hI.aestronglyMeasurable
  calc
    _ = ∫ ω,rankReachValue ((L).randomizedPolicy P) i ω ∂((L).randomizedPolicy P).worldLaw P :=
      (rankReachValue_integral P ((L).randomizedPolicy P) i).symm
    _ = ∫ ω,f (jointRankWorld (rawRankWorld ω)) ∂((L).randomizedPolicy P).worldLaw P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        have he := RankPolicy.reaches_iff_of_actions_eq _ _ _ _ _ _
          (rawRank_action P νT νP times mu zlo zhi targetEstimate policyEstimate hT hC ω) i
        change (if (L).policy.Reaches ω.2.2 ω.2.1 ω.1 i then (1 : ℝ) else 0) =
          (if (Q).rule.Reaches ((rankCalibrationExperiment ω.2.2).1,
            (rankCalibrationExperiment ω.2.2).2) ω.2.1 ω.1 i then (1 : ℝ) else 0)
        by_cases hi : (L).policy.Reaches ω.2.2 ω.2.1 ω.1 i
        · rw [if_pos hi,if_pos (he.mp hi)]
        · rw [if_neg hi,if_neg (fun hj => hi (he.mpr hj))]
    _ = ∫ w,(f ∘ jointRankWorld) w ∂(O).prod (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod N)) := hMap
    _ = (∫ d,∫ w,(f ∘ jointRankWorld) (d,w)
        ∂P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod N) ∂O) := integral_prod _ hI
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun d => (integral_congr_ae
        (Filter.Eventually.of_forall fun w => by
          have he := RankPolicy.reaches_iff_of_actions_eq _ _ _ _ _ _
            (jointRank_action P νT νP times mu zlo zhi targetEstimate policyEstimate hT hC d w.2.2 w.2.1 w.1) i
          simp only [f,rankReachValue,Function.comp_def,jointRankWorld,he])).trans (rankReachValue_integral P (C d) i)

include hT in
lemma integrable_idealRankConditionalReward (hP : Integrable Instance.maximum P.valuesLaw) :
    Integrable (fun d => (C d).expectedReward P) O := by
  have hM := jointRankWorld_measurePreserving (m := m) (J := J) P νT νP times
  have hI := (hM.integrable_comp_of_integrable ((Q).integrable_realizedReward P hP)).integral_prod_left
  apply hI.congr
  exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun w =>
    RankPolicy.reward_eq_of_actions_eq _ _ _ _ _ _
      (jointRank_action P νT νP times mu zlo zhi targetEstimate policyEstimate hT hC d w.2.2 w.2.1 w.1))

include hT in
lemma integrable_idealRankConditionalReach (i : Fin n) :
    Integrable (fun d => (C d).reachProbability P i) O := by
  have hM := jointRankWorld_measurePreserving (m := m) (J := J) P νT νP times
  have hI := (hM.integrable_comp_of_integrable (rankReachValue_integrable P Q i)).integral_prod_left
  apply hI.congr
  exact Filter.Eventually.of_forall fun d => (integral_congr_ae
    (Filter.Eventually.of_forall fun w => by
      have he := RankPolicy.reaches_iff_of_actions_eq _ _ _ _ _ _
        (jointRank_action P νT νP times mu zlo zhi targetEstimate policyEstimate hT hC d w.2.2 w.2.1 w.1) i
      simp only [rankReachValue,Function.comp_def,jointRankWorld,he])).trans (rankReachValue_integral P (C d) i)

end

end ProphetSecretary.Statistics.Calibration

/-!
# Statistical equality for the ideal rounded rank implementation

The comparison couples the whole validation profiles and the actual
online execution. The policy does not observe the underlying continuous
times. Only the rank and its assigned numerical timestamp are used.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

section

variable (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
  [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
  {f : ℝ → ℝ} (hf : Measurable f)
  (hRound : ∀ t∈Icc (0 : ℝ) 1, f t∈Icc (0 : ℝ) t)
  (mu : ℝ) {zlo zhi : ℝ} (h0 : 0≤zlo) (hz : zlo≤zhi)
  (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
  (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
  (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
    policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "D" => RankCalibrationOffline n m J TSeed PSeed
local notation "S" => Instance.sortedTimesLaw n
local notation "Sround" => mappedSortedClockLaw n f hf
local notation "O" => Measure.prod (firstInformationLaw (m := m) P νT) (Measure.pi (fun _ : Fin m =>
    rankValidationProfileLaw (J := J) P νP S))
local notation "Orank" => Measure.prod (firstInformationLaw (m := m) P νT) (Measure.pi (fun _ : Fin m =>
    rankValidationProfileLaw (J := J) P νP Sround))
local notation "A" => reportedOfflinePrepare (J := J) (terminalClockReport f) mu zlo zhi targetEstimate
    (clockRoundedEstimate f policyEstimate)
local notation "hA" => measurable_reportedOfflinePrepare (J := J) (terminalClockReport f)
    (measurable_terminalClockReport hf) mu zlo zhi targetEstimate (clockRoundedEstimate f policyEstimate)
    hT (measurable_clockRoundedEstimate hf policyEstimate hC)
local notation "N" => onlineCalibrationSeedLaw (n := n) (J := J) νP
local notation "L" => selectorLearner νT νP zlo zhi (clockRoundedEstimate f policyEstimate) A hA
    (measurable_clockRoundedEstimate hf policyEstimate hC)

local notation "R" => rankCalibratedLearner (J := J) νT νP (Instance.uniformPermutationLaw n)
    Sround Instance.uniformClock id measurable_id mu zlo zhi targetEstimate policyEstimate hT hC

def rankOfflineRound (d : D) : D :=
  (d.1,fun j => roundRankValidationProfile f (d.2 j))

def rankOfflineReconstruct (d : D) : OfflineData n m J TSeed PSeed :=
  (d.1,fun j => rankValidationProfileWorld (d.2 j))

omit [NeZero m] in
lemma rankOfflineRound_measurePreserving :
    MeasurePreserving (rankOfflineRound (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed) (f := f)) O Orank := by
  exact (MeasurePreserving.id (firstInformationLaw (m := m) P νT)).prod (measurePreserving_pi
    (fun _ : Fin m => rankValidationProfileLaw (J := J) P νP S)
    (fun _ : Fin m => rankValidationProfileLaw (J := J) P νP Sround)
    (fun _ => roundRankValidationProfile_measurePreserving P νP hf))

omit [NeZero m] in
lemma rankOfflineReconstruct_measurePreserving :
    MeasurePreserving (rankOfflineReconstruct (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed))
      O (offlineDataLaw P νT νP) := by
  exact (MeasurePreserving.id (firstInformationLaw (m := m) P νT)).prod (measurePreserving_pi
    (fun _ : Fin m => rankValidationProfileLaw (J := J) P νP S)
    (fun _ : Fin m => P.worldLaw (policyQueryArrayLaw (J := J) νP))
    (fun _ => rankValidationProfileWorld_measurePreserving P νP))

include hRound h0 hz in
theorem idealRankCalibratedLearner_reported_reward_eq (hP : Integrable Instance.maximum P.valuesLaw) :
    (R).expectedReward P=(L).expectedReward P := by
  let V := rankValidationPrepare (J := J) mu zlo zhi targetEstimate policyEstimate
  let g := fun d : D => (roundedPreparedRankPolicy (J := J) νP Sround zlo zhi policyEstimate hC (V d)).expectedReward P
  let u := fun d : OfflineData n m J TSeed PSeed =>
    (selectorConditionalPolicy νP zlo zhi (clockRoundedEstimate f policyEstimate) A
      (measurable_clockRoundedEstimate hf policyEstimate hC) d).expectedReward P
  have hRg := idealRankCalibratedLearner_reward_eq_integral (J := J) P νT νP Sround mu zlo zhi
    targetEstimate policyEstimate hT hC hP
  have hLu := selectorLearner_expectedReward_eq_integral P νT νP zlo zhi (clockRoundedEstimate f policyEstimate)
    A hA (measurable_clockRoundedEstimate hf policyEstimate hC) hP
  have hg : Integrable g Orank := integrable_idealRankConditionalReward (J := J) P νT νP Sround
    mu zlo zhi targetEstimate policyEstimate hT hC hP
  have hu := integrable_selectorConditionalReward P νT νP zlo zhi (clockRoundedEstimate f policyEstimate)
    A hA (measurable_clockRoundedEstimate hf policyEstimate hC) hP
  have h1 := (rankOfflineRound_measurePreserving (m := m) (J := J) P νT νP hf).hasLaw.integral_comp hg.aestronglyMeasurable
  have h2 := (rankOfflineReconstruct_measurePreserving (m := m) (J := J) P νT νP).hasLaw.integral_comp hu.aestronglyMeasurable
  rw [hRg,hLu]
  calc
    _ = ∫ d,g (rankOfflineRound (f := f) d) ∂O := h1.symm
    _ = ∫ d,u (rankOfflineReconstruct d) ∂O := by
      apply integral_congr_ae
      filter_upwards [rankValidationPrepare_eq_reported_ae (J := J) P νT νP h0 hz f hRound mu
        targetEstimate policyEstimate] with d hd
      change V (rankOfflineRound (f := f) d)=A (rankOfflineReconstruct d) at hd
      change (roundedPreparedRankPolicy (J := J) νP Sround zlo zhi policyEstimate hC
        (V (rankOfflineRound (f := f) d))).expectedReward P=_
      rw [hd]
      exact roundedPreparedRankPolicy_expectedReward_eq (J := J) P νP hf h0 hz hRound policyEstimate hC _ hP
    _ = _ := h2

include hRound h0 hz in
theorem idealRankCalibratedLearner_reported_reach_eq (i : Fin n) :
    (R).reachProbability P i=(L).reachProbability P i := by
  let V := rankValidationPrepare (J := J) mu zlo zhi targetEstimate policyEstimate
  let g := fun d : D => (roundedPreparedRankPolicy (J := J) νP Sround zlo zhi policyEstimate hC (V d)).reachProbability P i
  let u := fun d : OfflineData n m J TSeed PSeed =>
    (selectorConditionalPolicy νP zlo zhi (clockRoundedEstimate f policyEstimate) A
      (measurable_clockRoundedEstimate hf policyEstimate hC) d).rule.reachProbability P N i
  have hRg := idealRankCalibratedLearner_reach_eq_integral (J := J) P νT νP Sround mu zlo zhi
    targetEstimate policyEstimate hT hC i
  have hLu := selectorLearner_reachProbability_eq_integral P νT νP zlo zhi (clockRoundedEstimate f policyEstimate)
    A hA (measurable_clockRoundedEstimate hf policyEstimate hC) i
  have hg : Integrable g Orank := integrable_idealRankConditionalReach (J := J) P νT νP Sround
    mu zlo zhi targetEstimate policyEstimate hT hC i
  have hu := integrable_selectorConditionalReach P νT νP zlo zhi (clockRoundedEstimate f policyEstimate)
    A hA (measurable_clockRoundedEstimate hf policyEstimate hC) i
  have h1 := (rankOfflineRound_measurePreserving (m := m) (J := J) P νT νP hf).hasLaw.integral_comp hg.aestronglyMeasurable
  have h2 := (rankOfflineReconstruct_measurePreserving (m := m) (J := J) P νT νP).hasLaw.integral_comp hu.aestronglyMeasurable
  rw [hRg,hLu]
  calc
    _ = ∫ d,g (rankOfflineRound (f := f) d) ∂O := h1.symm
    _ = ∫ d,u (rankOfflineReconstruct d) ∂O := by
      apply integral_congr_ae
      filter_upwards [rankValidationPrepare_eq_reported_ae (J := J) P νT νP h0 hz f hRound mu
        targetEstimate policyEstimate] with d hd
      change V (rankOfflineRound (f := f) d)=A (rankOfflineReconstruct d) at hd
      change (roundedPreparedRankPolicy (J := J) νP Sround zlo zhi policyEstimate hC
        (V (rankOfflineRound (f := f) d))).reachProbability P i=_
      rw [hd]
      exact roundedPreparedRankPolicy_reachProbability_eq (J := J) P νP hf h0 hz hRound policyEstimate hC _ i
    _ = _ := h2

end

end ProphetSecretary.Statistics.Calibration
