import ProphetSecretary.Statistics.CalibratedConditioning

/-!
# Executing a measurable offline selector

The prepared point is computed before any online arrival. This common
execution allows the same independence and conditioning proof for selectors
based on exact or reported validation durations.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

section

variable (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
  (zlo zhi : ℝ) (policyEstimate : ContinuationEstimator n m PSeed)
  (A : OfflineData n m J TSeed PSeed → PreparedCalibration n m) (hA : Measurable A)
  (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
    policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "Raw" => Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed

noncomputable def selectorSamplePolicy : Policy Raw n where
  decide p t i x H := decidePrepared zlo zhi policyEstimate (A (calibratedOfflineData p))
    p.2.2.2.1 p.2.2.2.2 t i x H

include νT νP hA hC in
lemma selectorSamplePolicy_isMeasurable : (selectorSamplePolicy zlo zhi policyEstimate A).IsMeasurable := by
  let Ω := Raw × (ℝ × (Fin n × (ℝ × History n)))
  let E := (Reservoir n m × PolicyQueryArray n J PSeed) × (ℝ × (Fin n × (ℝ × History n)))
  have hD := (calibratedOfflineData_measurePreserving (m := m) (J := J) (zeroInstance n) νT νP).measurable
  have hP : Measurable (fun p : Ω => A (calibratedOfflineData p.1)) := hA.comp (hD.comp measurable_fst)
  have hR : Measurable (fun p : Ω => p.1.2.2.2.1) := by fun_prop
  have hCoin : Measurable (fun p : Ω => p.1.2.2.2.2) := by fun_prop
  have hIndex := measurable_mixturePolicyIndex (J := J) (measurable_snd.comp hP) hCoin
  have hEval : Measurable (fun p : E × Fin (J+1) =>
      (numericalFamilyPolicy zlo zhi policyEstimate p.2).decide p.1.1 p.1.2.1
        p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2) :=
    measurable_from_prod_countable_left (fun j => numericalFamilyPolicy_isMeasurable zlo zhi policyEstimate hC j)
  change Measurable (fun p : Ω => (numericalFamilyPolicy zlo zhi policyEstimate
      (mixturePolicyIndex J (A (calibratedOfflineData p.1)).2 p.1.2.2.2.2)).decide
        ((A (calibratedOfflineData p.1)).1,p.1.2.2.2.1) p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  have h := hEval.comp ((((measurable_fst.comp hP).prodMk hR).prodMk measurable_snd).prodMk hIndex)
  simpa only [Function.comp_def] using h

noncomputable def selectorLearner : Learner n (2*m) :=
  Learner.ofComputedSamplePolicy (CalibratedSeed n m J TSeed PSeed) (calibratedSeedLaw νT νP)
    (selectorSamplePolicy zlo zhi policyEstimate A)
    (selectorSamplePolicy_isMeasurable νT νP zlo zhi policyEstimate A hA hC)

lemma selectorLearner_decide (y : Reservoir n (2*m)) (r : CalibratedSeed n m J TSeed PSeed)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (selectorLearner νT νP zlo zhi policyEstimate A hA hC).policy.decide (y,r) t i x H =
      (selectorSamplePolicy zlo zhi policyEstimate A).decide (y,r) t i x H :=
  Learner.ofComputedSamplePolicy_decide _ _ _ _ y r t i x H

lemma selectorLearner_requests_eq (y : Reservoir n (2*m)) (r : CalibratedSeed n m J TSeed PSeed) (i : Fin n) :
    requests (trainingTranscript (selectorLearner νT νP zlo zhi policyEstimate A hA hC).request r y) i=2*m :=
  Learner.ofComputedSamplePolicy_requests_eq _ _ _ _ y r i

end

section

variable (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
  [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
  (zlo zhi : ℝ) (policyEstimate : ContinuationEstimator n m PSeed)
  (A : OfflineData n m J TSeed PSeed → PreparedCalibration n m) (hA : Measurable A)
  (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
    policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "D" => OfflineData n m J TSeed PSeed
local notation "S" => OnlineCalibrationSeed n J PSeed
local notation "O" => offlineDataLaw (m := m) (J := J) P νT νP
local notation "N" => onlineCalibrationSeedLaw (n := n) (J := J) νP
/-- The randomized policy deployed after conditioning on the offline data. -/
noncomputable def selectorConditionalPolicy (d : D) : RandomizedPolicy n :=
  RandomizedPolicy.ofRule N (preparedPolicy zlo zhi policyEstimate (A d))
    (preparedPolicy_isMeasurable zlo zhi policyEstimate hC (A d))

noncomputable def selectorOnlineRule : Policy (D × S) n where
  decide p t i x H := decidePrepared zlo zhi policyEstimate (A p.1) p.2.1 p.2.2 t i x H

include hA hC in
lemma selectorOnlineRule_isMeasurable : (selectorOnlineRule zlo zhi policyEstimate A).IsMeasurable := by
  let Ω := (D × S) × (ℝ × (Fin n × (ℝ × History n)))
  let E := (Reservoir n m × PolicyQueryArray n J PSeed) × (ℝ × (Fin n × (ℝ × History n)))
  have hP : Measurable (fun p : Ω => A p.1.1) := hA.comp (measurable_fst.comp measurable_fst)
  have hR : Measurable (fun p : Ω => p.1.2.1) := by fun_prop
  have hCoin : Measurable (fun p : Ω => p.1.2.2) := by fun_prop
  have hIndex := measurable_mixturePolicyIndex (J := J) (measurable_snd.comp hP) hCoin
  have hEval : Measurable (fun p : E × Fin (J+1) =>
      (numericalFamilyPolicy zlo zhi policyEstimate p.2).decide p.1.1 p.1.2.1
        p.1.2.2.1 p.1.2.2.2.1 p.1.2.2.2.2) :=
    measurable_from_prod_countable_left (fun j => numericalFamilyPolicy_isMeasurable zlo zhi policyEstimate hC j)
  change Measurable (fun p : Ω => (numericalFamilyPolicy zlo zhi policyEstimate
      (mixturePolicyIndex J (A p.1.1).2 p.1.2.2)).decide ((A p.1.1).1,p.1.2.1)
        p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  have h := hEval.comp ((((measurable_fst.comp hP).prodMk hR).prodMk measurable_snd).prodMk hIndex)
  simpa only [Function.comp_def] using h

noncomputable def selectorOnlinePolicy : RandomizedPolicy n :=
  RandomizedPolicy.ofRule ((O).prod N) (selectorOnlineRule zlo zhi policyEstimate A)
    (selectorOnlineRule_isMeasurable zlo zhi policyEstimate A hA hC)

local notation "Q" => selectorOnlinePolicy P νT νP zlo zhi policyEstimate A hA hC
local notation "C" => selectorConditionalPolicy νP zlo zhi policyEstimate A hC
local notation "L" => selectorLearner νT νP zlo zhi policyEstimate A hA hC

private lemma selector_conditional_outcomes (p : D × World n S) :
    (Q).realizedReward (mergeOfflineWorld p)=(C p.1).realizedReward p.2 ∧
    (Q).realizedDuration (mergeOfflineWorld p)=(C p.1).realizedDuration p.2 := by
  apply Policy.outcomes_eq_of_actions_eq
  intro i
  exact (preparedPolicy_decide zlo zhi policyEstimate (A p.1) p.2.2.2.1 p.2.2.2.2 _ i _ _).symm

private lemma selector_learner_outcomes (ω : World n (Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed)) :
    ((L).randomizedPolicy P).realizedReward ω=(Q).realizedReward (mergeOfflineWorld (splitCalibratedWorld ω)) ∧
    ((L).randomizedPolicy P).realizedDuration ω=(Q).realizedDuration (mergeOfflineWorld (splitCalibratedWorld ω)) := by
  apply Policy.outcomes_eq_of_actions_eq
  intro i
  exact selectorLearner_decide νT νP zlo zhi policyEstimate A hA hC
    ω.2.2.1 ω.2.2.2 _ i _ _

theorem selectorLearner_expectedReward_eq_integral (hP : Integrable Instance.maximum P.valuesLaw) :
    (L).expectedReward P = ∫ d, (C d).expectedReward P ∂O := by
  have hMerge := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hSplit := splitCalibratedWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := hMerge.integrable_comp_of_integrable ((Q).integrable_realizedReward P hP)
  have hMap := hSplit.hasLaw.integral_comp hI.aestronglyMeasurable
  calc
    _ = ∫ ω, ((Q).realizedReward ∘ mergeOfflineWorld ∘ splitCalibratedWorld) ω
        ∂P.worldLaw ((P.reservoirLaw (2*m)).prod (L).seedLaw) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (selector_learner_outcomes P νT νP zlo zhi policyEstimate A hA hC ω).1)
    _ = ∫ p, ((Q).realizedReward ∘ mergeOfflineWorld) p ∂(O).prod (P.worldLaw N) := hMap
    _ = (∫ d, ∫ ω, ((Q).realizedReward ∘ mergeOfflineWorld) (d,ω) ∂P.worldLaw N ∂O) := integral_prod _ hI
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (selector_conditional_outcomes P νT νP zlo zhi policyEstimate A hA hC (d,ω)).1)

theorem selectorLearner_meanDuration_eq_integral :
    (L).meanDuration P = ∫ d, (C d).expectedDuration P ∂O := by
  have hMerge := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hSplit := splitCalibratedWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := hMerge.integrable_comp_of_integrable ((Q).integrable_realizedDuration P)
  have hMap := hSplit.hasLaw.integral_comp hI.aestronglyMeasurable
  calc
    _ = ∫ ω, ((Q).realizedDuration ∘ mergeOfflineWorld ∘ splitCalibratedWorld) ω
        ∂P.worldLaw ((P.reservoirLaw (2*m)).prod (L).seedLaw) :=
      integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (selector_learner_outcomes P νT νP zlo zhi policyEstimate A hA hC ω).2)
    _ = ∫ p, ((Q).realizedDuration ∘ mergeOfflineWorld) p ∂(O).prod (P.worldLaw N) := hMap
    _ = (∫ d, ∫ ω, ((Q).realizedDuration ∘ mergeOfflineWorld) (d,ω) ∂P.worldLaw N ∂O) := integral_prod _ hI
    _ = _ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun ω =>
        (selector_conditional_outcomes P νT νP zlo zhi policyEstimate A hA hC (d,ω)).2)

private lemma integrable_selector_reach (i : Fin n) :
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

theorem selectorLearner_reachProbability_eq_integral (i : Fin n) :
    (L).reachProbability P i = ∫ d, (C d).rule.reachProbability P N i ∂O := by
  let f := fun ω : (Q).World => (Q).rule.reachIndicator ω.2.2 ω.1 ω.2.1 i
  have hMerge := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hSplit := splitCalibratedWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := hMerge.integrable_comp_of_integrable
    (integrable_selector_reach P νT νP zlo zhi policyEstimate A hA hC i)
  have hMap := hSplit.hasLaw.integral_comp hI.aestronglyMeasurable
  calc
    _ = ∫ ω, (f ∘ mergeOfflineWorld ∘ splitCalibratedWorld) ω
        ∂P.worldLaw ((P.reservoirLaw (2*m)).prod (L).seedLaw) := by
      rw [Learner.reachProbability,(L).policy.reachProbability_eq_integral_indicator (L).policy_isMeasurable]
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω => by
        have h := (selector_learner_outcomes P νT νP zlo zhi policyEstimate A hA hC ω).2
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
        have h := (selector_conditional_outcomes P νT νP zlo zhi policyEstimate A hA hC (d,ω)).2
        change (Q).rule.stoppingTime (d,ω.2.2) Finset.univ ω.1 ω.2.1 =
          (C d).rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 at h
        simp only [f,Policy.reachIndicator,Policy.Reaches,Function.comp_def,mergeOfflineWorld,h]
        split_ifs <;> rfl

include hA in
theorem integrable_selectorConditionalReward (hP : Integrable Instance.maximum P.valuesLaw) :
    Integrable (fun d => (C d).expectedReward P) O := by
  have hM := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := (hM.integrable_comp_of_integrable ((Q).integrable_realizedReward P hP)).integral_prod_left
  apply hI.congr
  exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    (selector_conditional_outcomes P νT νP zlo zhi policyEstimate A hA hC (d,ω)).1)

include hA in
theorem integrable_selectorConditionalDuration :
    Integrable (fun d => (C d).expectedDuration P) O := by
  have hM := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := (hM.integrable_comp_of_integrable ((Q).integrable_realizedDuration P)).integral_prod_left
  apply hI.congr
  exact Filter.Eventually.of_forall fun d => integral_congr_ae (Filter.Eventually.of_forall fun ω =>
    (selector_conditional_outcomes P νT νP zlo zhi policyEstimate A hA hC (d,ω)).2)

include hA in
theorem integrable_selectorConditionalReach (i : Fin n) :
    Integrable (fun d => (C d).rule.reachProbability P N i) O := by
  have hM := mergeOfflineWorld_measurePreserving (m := m) (J := J) P νT νP
  have hI := (hM.integrable_comp_of_integrable
    (integrable_selector_reach P νT νP zlo zhi policyEstimate A hA hC i)).integral_prod_left
  apply hI.congr
  exact Filter.Eventually.of_forall fun d => by
    refine (integral_congr_ae (Filter.Eventually.of_forall (fun ω : World n S => ?_))).trans
      ((C d).rule.reachProbability_eq_integral_indicator (C d).measurable_rule P N i).symm
    have h := (selector_conditional_outcomes P νT νP zlo zhi policyEstimate A hA hC (d,ω)).2
    change (Q).rule.stoppingTime (d,ω.2.2) Finset.univ ω.1 ω.2.1 =
      (C d).rule.stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 at h
    simp only [Policy.reachIndicator,Policy.Reaches,Function.comp_def,mergeOfflineWorld,h]
    split_ifs <;> rfl

end

end ProphetSecretary.Statistics.Calibration
