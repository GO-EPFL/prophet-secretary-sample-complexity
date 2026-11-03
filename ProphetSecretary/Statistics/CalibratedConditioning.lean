import ProphetSecretary.Statistics.CalibratedOfflineLaw

/-!
# Reward, duration and reach after fixing offline data

Fubini on the actual regrouped world law identifies the learner's outcomes
with averages of the independently executed prepared policies.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

section Conditioning

variable (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
  [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
  (mu zlo zhi : ℝ) (targetEstimate : TargetEstimator n m TSeed)
  (policyEstimate : ContinuationEstimator n m PSeed)
  (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
  (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
    policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "D" => OfflineData n m J TSeed PSeed
local notation "S" => OnlineCalibrationSeed n J PSeed
local notation "O" => offlineDataLaw (m := m) (J := J) P νT νP
local notation "N" => onlineCalibrationSeedLaw (n := n) (J := J) νP
local notation "A" => offlinePrepare (J := J) mu zlo zhi targetEstimate policyEstimate

/-- The randomized policy deployed after conditioning on the offline data. -/
noncomputable def conditionalCalibrationPolicy (d : D) : RandomizedPolicy n :=
  RandomizedPolicy.ofRule N (preparedPolicy zlo zhi policyEstimate (A d))
    (preparedPolicy_isMeasurable zlo zhi policyEstimate hC (A d))

noncomputable def offlineOnlineRule : Policy (D × S) n where
  decide p t i x H := decidePrepared zlo zhi policyEstimate (A p.1) p.2.1 p.2.2 t i x H

include hT hC in
lemma offlineOnlineRule_isMeasurable : (offlineOnlineRule (J := J) mu zlo zhi targetEstimate policyEstimate).IsMeasurable := by
  let Ω := (D × S) × (ℝ × (Fin n × (ℝ × History n)))
  let E := (Reservoir n m × PolicyQueryArray n J PSeed) × (ℝ × (Fin n × (ℝ × History n)))
  have hA : Measurable (fun p : Ω => A p.1.1) :=
    (measurable_offlinePrepare mu zlo zhi targetEstimate policyEstimate hT hC).comp
      (measurable_fst.comp measurable_fst)
  have hR : Measurable (fun p : Ω => p.1.2.1) := by fun_prop
  have hCoin : Measurable (fun p : Ω => p.1.2.2) := by fun_prop
  have hIndex := measurable_mixturePolicyIndex (J := J) (measurable_snd.comp hA) hCoin
  have hEval : Measurable (fun p : E × Fin (J+1) =>
      (numericalFamilyPolicy zlo zhi policyEstimate p.2).decide p.1.1 p.1.2.1
        p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2) :=
    measurable_from_prod_countable_left (fun j => numericalFamilyPolicy_isMeasurable zlo zhi policyEstimate hC j)
  change Measurable (fun p : Ω => (numericalFamilyPolicy zlo zhi policyEstimate
      (mixturePolicyIndex J (A p.1.1).2 p.1.2.2)).decide ((A p.1.1).1,p.1.2.1)
        p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  have h := hEval.comp ((((measurable_fst.comp hA).prodMk hR).prodMk measurable_snd).prodMk hIndex)
  simpa only [Function.comp_def] using h

noncomputable def offlineOnlinePolicy : RandomizedPolicy n :=
  RandomizedPolicy.ofRule ((O).prod N) (offlineOnlineRule mu zlo zhi targetEstimate policyEstimate)
    (offlineOnlineRule_isMeasurable (J := J) mu zlo zhi targetEstimate policyEstimate hT hC)

def mergeOfflineWorld (p : D × World n S) : World n (D × S) :=
  (p.2.1,p.2.2.1,p.1,p.2.2.2)

omit [NeZero m] in
lemma mergeOfflineWorld_measurePreserving :
    MeasurePreserving (mergeOfflineWorld (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed))
      ((O).prod (P.worldLaw N)) (P.worldLaw ((O).prod N)) := by
  let X := P.valuesLaw
  let U := Instance.clocksLaw n
  have h1 := (MeasurePreserving.id O).prod ((measurePreserving_prodAssoc X U N).symm MeasurableEquiv.prodAssoc)
  have h2 := (measurePreserving_prodAssoc O (X.prod U) N).symm MeasurableEquiv.prodAssoc
  have h3 := (Measure.measurePreserving_swap (μ := O) (ν := X.prod U)).prod (MeasurePreserving.id N)
  have h4 := measurePreserving_prodAssoc (X.prod U) O N
  have h5 := measurePreserving_prodAssoc X U ((O).prod N)
  exact h5.comp (h4.comp (h3.comp (h2.comp h1)))

local notation "Q" => offlineOnlinePolicy (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC
local notation "C" => conditionalCalibrationPolicy (J := J) νP mu zlo zhi targetEstimate policyEstimate hC
local notation "L" => learnerCore (J := J) mu zlo zhi νT νP targetEstimate policyEstimate hT hC

private lemma conditional_outcomes (p : D × World n S) :
    (Q).realizedReward (mergeOfflineWorld p)=(C p.1).realizedReward p.2 ∧
    (Q).realizedDuration (mergeOfflineWorld p)=(C p.1).realizedDuration p.2 := by
  apply Policy.outcomes_eq_of_actions_eq
  intro i
  exact (preparedPolicy_decide zlo zhi policyEstimate (A p.1) p.2.2.2.1 p.2.2.2.2 _ i _ _).symm

private lemma learner_outcomes (ω : World n (Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed)) :
    ((L).randomizedPolicy P).realizedReward ω=(Q).realizedReward (mergeOfflineWorld (splitCalibratedWorld ω)) ∧
    ((L).randomizedPolicy P).realizedDuration ω=(Q).realizedDuration (mergeOfflineWorld (splitCalibratedWorld ω)) := by
  apply Policy.outcomes_eq_of_actions_eq
  intro i
  exact learnerCore_decide mu zlo zhi νT νP targetEstimate policyEstimate hT hC
    ω.2.2.1 ω.2.2.2 _ i _ _

theorem learnerCore_expectedReward_eq_integral (hP : Integrable Instance.maximum P.valuesLaw) :
    (L).expectedReward P = ∫ d, (C d).expectedReward P ∂O := by
  have hMerge := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hSplit := splitCalibratedWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := hMerge.integrable_comp_of_integrable ((Q).integrable_realizedReward P hP)
  have hMap := hSplit.hasLaw.integral_comp hI.aestronglyMeasurable
  calc
    _ = ∫ ω, ((Q).realizedReward ∘ mergeOfflineWorld ∘ splitCalibratedWorld) ω
        ∂P.worldLaw ((P.reservoirLaw (2*m)).prod (L).seedLaw) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (learner_outcomes (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC ω).1)
    _ = ∫ p, ((Q).realizedReward ∘ mergeOfflineWorld) p ∂(O).prod (P.worldLaw N) := hMap
    _ = (∫ d, ∫ ω, ((Q).realizedReward ∘ mergeOfflineWorld) (d,ω) ∂P.worldLaw N ∂O) := integral_prod _ hI
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (conditional_outcomes (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC (d,ω)).1)

theorem learnerCore_meanDuration_eq_integral :
    (L).meanDuration P = ∫ d, (C d).expectedDuration P ∂O := by
  have hMerge := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hSplit := splitCalibratedWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := hMerge.integrable_comp_of_integrable ((Q).integrable_realizedDuration P)
  have hMap := hSplit.hasLaw.integral_comp hI.aestronglyMeasurable
  calc
    _ = ∫ ω, ((Q).realizedDuration ∘ mergeOfflineWorld ∘ splitCalibratedWorld) ω
        ∂P.worldLaw ((P.reservoirLaw (2*m)).prod (L).seedLaw) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (learner_outcomes (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC ω).2)
    _ = ∫ p, ((Q).realizedDuration ∘ mergeOfflineWorld) p ∂(O).prod (P.worldLaw N) := hMap
    _ = (∫ d, ∫ ω, ((Q).realizedDuration ∘ mergeOfflineWorld) (d,ω) ∂P.worldLaw N ∂O) := integral_prod _ hI
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (conditional_outcomes (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC (d,ω)).2)

private lemma integrable_conditioned_reach (i : Fin n) :
    Integrable (fun ω : (Q).World => (Q).rule.reachIndicator ω.2.2 ω.1 ω.2.1 i)
      (P.worldLaw (Q).seedLaw) := by
  have hm := (Q).rule.measurable_reachIndicator (Q).measurable_rule
    (measurable_snd.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i
  apply Integrable.of_bound hm.aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun ω => by
    have h := (Q).rule.reachIndicator_mem_unit ω.2.2 ω.1 ω.2.1 i
    change ‖(Q).rule.reachIndicator ω.2.2 ω.1 ω.2.1 i‖≤1
    rw [Real.norm_eq_abs,abs_of_nonneg h.1]
    exact h.2

theorem learnerCore_reachProbability_eq_integral (i : Fin n) :
    (L).reachProbability P i = ∫ d, (C d).rule.reachProbability P N i ∂O := by
  let f := fun ω : (Q).World => (Q).rule.reachIndicator ω.2.2 ω.1 ω.2.1 i
  have hMerge := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hSplit := splitCalibratedWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := hMerge.integrable_comp_of_integrable
    (integrable_conditioned_reach (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC i)
  have hMap := hSplit.hasLaw.integral_comp hI.aestronglyMeasurable
  calc
    _ = ∫ ω, (f ∘ mergeOfflineWorld ∘ splitCalibratedWorld) ω
        ∂P.worldLaw ((P.reservoirLaw (2*m)).prod (L).seedLaw) := by
      rw [Learner.reachProbability,(L).policy.reachProbability_eq_integral_indicator (L).policy_isMeasurable]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        have h := (learner_outcomes (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC ω).2
        change (L).policy.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 =
          (Q).rule.stoppingTime (calibratedOfflineData ω.2.2,ω.2.2.2.2.2) Finset.univ ω.1 ω.2.1 at h
        simp only [f,Policy.reachIndicator,Policy.Reaches,Function.comp_def,mergeOfflineWorld,splitCalibratedWorld]
        simp only [h]
        split_ifs <;> rfl
    _ = ∫ p, (f ∘ mergeOfflineWorld) p ∂(O).prod (P.worldLaw N) := hMap
    _ = (∫ d, ∫ ω, (f ∘ mergeOfflineWorld) (d,ω) ∂P.worldLaw N ∂O) := integral_prod _ hI
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun d => by
        refine (integral_congr_ae (Filter.Eventually.of_forall (fun ω : World n S => ?_))).trans
          ((C d).rule.reachProbability_eq_integral_indicator (C d).measurable_rule P N i).symm
        have h := (conditional_outcomes (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC (d,ω)).2
        change (Q).rule.stoppingTime (d,ω.2.2) Finset.univ ω.1 ω.2.1 =
          (C d).rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 at h
        simp only [f,Policy.reachIndicator,Policy.Reaches,Function.comp_def,mergeOfflineWorld,h]
        split_ifs <;> rfl

include hT in
theorem integrable_conditionalCalibrationReward (hP : Integrable Instance.maximum P.valuesLaw) :
    Integrable (fun d => (C d).expectedReward P) O := by
  have hM := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := (hM.integrable_comp_of_integrable ((Q).integrable_realizedReward P hP)).integral_prod_left
  apply hI.congr
  exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    (conditional_outcomes (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC (d,ω)).1)

include hT in
theorem integrable_conditionalCalibrationDuration :
    Integrable (fun d => (C d).expectedDuration P) O := by
  have hM := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := (hM.integrable_comp_of_integrable ((Q).integrable_realizedDuration P)).integral_prod_left
  apply hI.congr
  exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    (conditional_outcomes (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC (d,ω)).2)

include hT in
theorem integrable_conditionalCalibrationReach (i : Fin n) :
    Integrable (fun d => (C d).rule.reachProbability P N i) O := by
  have hM := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := (hM.integrable_comp_of_integrable
    (integrable_conditioned_reach (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC i)).integral_prod_left
  apply hI.congr
  exact Filter.Eventually.of_forall fun d => by
    refine (integral_congr_ae (Filter.Eventually.of_forall (fun ω : World n S => ?_))).trans
      ((C d).rule.reachProbability_eq_integral_indicator (C d).measurable_rule P N i).symm
    have h := (conditional_outcomes (J := J) P νT νP mu zlo zhi targetEstimate policyEstimate hT hC (d,ω)).2
    change (Q).rule.stoppingTime (d,ω.2.2) Finset.univ ω.1 ω.2.1 =
      (C d).rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 at h
    simp only [Policy.reachIndicator,Policy.Reaches,Function.comp_def,mergeOfflineWorld,h]
    split_ifs <;> rfl

end Conditioning

end ProphetSecretary.Statistics.Calibration
