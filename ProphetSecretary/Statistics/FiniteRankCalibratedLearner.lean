import ProphetSecretary.Statistics.RankCalibrationBits
import ProphetSecretary.Model.RankToClockLaw
import ProphetSecretary.Model.RankOutcomeAgreement

/-!
# The learner driven by actual finite key and clock arrays

The training request scan is the same as in the two-block construction.
Independent finite bit arrays are interpreted before use, and the online
callback observes only the exogenous rank prefix.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

private lemma dyadicGrid_positive (b : ℕ) : 0 < (2 : ℕ)^b := by positivity

section

variable (b c : ℕ) (νT : Measure TSeed) (νP : Measure PSeed)
  [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
  (mu zlo zhi : ℝ) (targetEstimate : TargetEstimator n m TSeed)
  (policyEstimate : ContinuationEstimator n m PSeed)
  (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
  (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
    policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2))

local notation "B" => RankCalibrationBits n m J b c TSeed PSeed
local notation "K" => Measure.map (roundedValidationPermutation (N := 2^b) (dyadicGrid_positive b)) (Instance.clocksLaw n)
local notation "S" => roundedSortedTimesLaw n (2^b) (dyadicGrid_positive b)
local notation "coinRound" => uniformGridRound (2^c) (dyadicGrid_positive c)
local notation "C" => Measure.map coinRound Instance.uniformClock
local notation "Ψ" => interpretRankCalibrationBits (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed) b c
local notation "π" => rankCalibratedSamplePolicy (J := J) coinRound mu zlo zhi targetEstimate policyEstimate
local notation "hπ" => rankCalibratedSamplePolicy_isMeasurable (J := J) coinRound
  (measurable_uniformGridRound _ _) mu zlo zhi targetEstimate policyEstimate hT hC

noncomputable def finiteRankSamplePolicy : RankPolicy (Reservoir n (2*m) × B) n where
  decide p k i x H := (π).decide (p.1,Ψ p.2) k i x H

include νT νP hT hC in
lemma finiteRankSamplePolicy_isMeasurable :
    (finiteRankSamplePolicy (J := J) b c mu zlo zhi targetEstimate policyEstimate).IsMeasurable := by
  let Ω := (Reservoir n (2*m) × B) × (Fin n × (Fin n × (ℝ × RankHistory n)))
  have h := interpretRankCalibrationBits_measurePreserving (n := n) (m := m) (J := J) b c νT νP
  have hF : Measurable (fun p : Ω => ((p.1.1,Ψ p.1.2),p.2)) :=
    ((measurable_fst.comp measurable_fst).prodMk (h.measurable.comp (measurable_snd.comp measurable_fst))).prodMk measurable_snd
  have he := (hπ).comp hF
  change Measurable (fun p : Ω => (π).decide (p.1.1,Ψ p.1.2)
    p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)
  simpa only [Function.comp_def] using he

noncomputable def finiteRankCalibratedLearner : RankLearner n (2*m) :=
  RankLearner.ofComputedSamplePolicy B (rankCalibrationBitsLaw b c νT νP)
    (finiteRankSamplePolicy b c mu zlo zhi targetEstimate policyEstimate)
    (finiteRankSamplePolicy_isMeasurable b c νT νP mu zlo zhi targetEstimate policyEstimate hT hC)

local instance finite_rank_order_probability : IsProbabilityMeasure K :=
  Measure.isProbabilityMeasure_map (measurable_roundedValidationPermutation n (2^b) (by positivity)).aemeasurable
local instance finite_rank_times_probability : IsProbabilityMeasure S := by
  unfold roundedSortedTimesLaw
  haveI : IsProbabilityMeasure ((Instance.clocksLaw n).map Instance.sortedClocks) :=
    Measure.isProbabilityMeasure_map Instance.measurable_sortedClocks.aemeasurable
  exact Measure.isProbabilityMeasure_map
    (measurable_pi_lambda _ (fun i => (measurable_uniformGridRound _ _).comp (measurable_pi_apply i))).aemeasurable
local instance finite_rank_coin_probability : IsProbabilityMeasure C :=
  Measure.isProbabilityMeasure_map (measurable_uniformGridRound _ _).aemeasurable

local notation "L" => finiteRankCalibratedLearner (J := J) b c νT νP mu zlo zhi targetEstimate policyEstimate hT hC
local notation "R" => rankCalibratedLearner (J := J) νT νP K S C coinRound (measurable_uniformGridRound _ _)
  mu zlo zhi targetEstimate policyEstimate hT hC

lemma finiteRankCalibratedLearner_requests_eq (y : Reservoir n (2*m)) (r : B) (i : Fin n) :
    requests (trainingTranscript (L).request r y) i=2*m :=
  RankLearner.ofComputedSamplePolicy_requests_eq _ _ _ _ y r i

lemma finiteRankCalibratedLearner_decide_eq (y : Reservoir n (2*m)) (r : B)
    (k i : Fin n) (x : ℝ) (H : RankHistory n) :
    (L).policy.decide (y,r) k i x H=(R).policy.decide (y,Ψ r) k i x H := by
  have hL : (L).policy.decide (y,r) k i x H=(π).decide (y,Ψ r) k i x H :=
    RankLearner.ofComputedSamplePolicy_decide _ _ _ _ y r k i x H
  have hR : (R).policy.decide (y,Ψ r) k i x H=(π).decide (y,Ψ r) k i x H :=
    RankLearner.ofComputedSamplePolicy_decide _ _ _ _ y (Ψ r) k i x H
  exact hL.trans hR.symm

@[simp] lemma finiteRankCalibratedLearner_accepts_cap (y : Reservoir n (2*m)) (r : B)
    (k i : Fin n) (H : RankHistory n) :
    (L).policy.decide (y,r) k i 1 H=true := by
  have hL : (L).policy.decide (y,r) k i 1 H=(π).decide (y,Ψ r) k i 1 H :=
    RankLearner.ofComputedSamplePolicy_decide _ _ _ _ y r k i 1 H
  rw [hL]
  simp only [rankCalibratedSamplePolicy,Policy.clockToRank,numericalFamilyPolicy_accepts_cap]

@[simp] lemma finiteRankCalibratedLearner_rejects_zero (y : Reservoir n (2*m)) (r : B)
    (k i : Fin n) (H : RankHistory n) :
    (L).policy.decide (y,r) k i 0 H=false := by
  have hL : (L).policy.decide (y,r) k i 0 H=(π).decide (y,Ψ r) k i 0 H :=
    RankLearner.ofComputedSamplePolicy_decide _ _ _ _ y r k i 0 H
  rw [hL]
  simp only [rankCalibratedSamplePolicy,Policy.clockToRank,numericalFamilyPolicy_rejects_zero]

private def finiteRankWorldMap
    (ω : (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n (2*m) × B))) :
    (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n (2*m) × RankCalibratedSeed n m J TSeed PSeed)) :=
  (ω.1,ω.2.1,ω.2.2.1,Ψ ω.2.2.2)

private lemma finiteRankWorldMap_measurePreserving (P : Instance n) :
    MeasurePreserving (finiteRankWorldMap (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed) b c)
      (((L).randomizedPolicy P).worldLaw P) (((R).randomizedPolicy P).worldLaw P) := by
  let T := P.reservoirLaw (2*m)
  haveI : IsProbabilityMeasure T := P.reservoirLaw_probability (2*m)
  have hR : MeasurePreserving (Prod.map id Ψ)
      (T.prod (rankCalibrationBitsLaw b c νT νP))
      (T.prod (rankCalibratedSeedLaw νT νP K S C)) :=
    (MeasurePreserving.id T).prod (interpretRankCalibrationBits_measurePreserving b c νT νP)
  exact (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod hR)

theorem finiteRankCalibratedLearner_reward_eq (P : Instance n) :
    (L).expectedReward P=(R).expectedReward P := by
  let f := finiteRankWorldMap (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed) b c
  let Q := (R).randomizedPolicy P
  have hMap := finiteRankWorldMap_measurePreserving (J := J) b c νT νP mu zlo zhi targetEstimate policyEstimate hT hC P
  calc
    _ = ∫ ω,Q.realizedReward (f ω) ∂((L).randomizedPolicy P).worldLaw P := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall fun ω =>
        RankPolicy.reward_eq_of_actions_eq _ _ _ _ _ _ (fun i =>
          finiteRankCalibratedLearner_decide_eq (J := J) b c νT νP mu zlo zhi targetEstimate policyEstimate hT hC
            ω.2.2.1 ω.2.2.2 _ i _ _)
    _ = _ := hMap.hasLaw.integral_comp Q.measurable_realizedReward.aestronglyMeasurable

theorem finiteRankCalibratedLearner_reach_eq (P : Instance n) (i : Fin n) :
    (L).reachProbability P i=(R).reachProbability P i := by
  let f := finiteRankWorldMap (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed) b c
  let Q := (R).randomizedPolicy P
  let μ := ((L).randomizedPolicy P).worldLaw P
  let E := {ω : Q.World | Q.rule.Reaches ω.2.2 ω.2.1 ω.1 i}
  have hE : MeasurableSet E := Q.rule.measurableSet_reaches Q.measurable_rule
    (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
    (fun j => (measurable_pi_apply j).comp measurable_fst) i
  have hMap := finiteRankWorldMap_measurePreserving (J := J) b c νT νP mu zlo zhi targetEstimate policyEstimate hT hC P
  have hEq : {ω | (L).policy.Reaches ω.2.2 ω.2.1 ω.1 i}=f ⁻¹' E := by
    ext ω
    exact RankPolicy.reaches_iff_of_actions_eq _ _ _ _ _ _ (fun k =>
      finiteRankCalibratedLearner_decide_eq (J := J) b c νT νP mu zlo zhi targetEstimate policyEstimate hT hC
        ω.2.2.1 ω.2.2.2 _ k _ _) i
  change μ.real {ω | (L).policy.Reaches ω.2.2 ω.2.1 ω.1 i}=(Q.worldLaw P).real E
  calc
    _ = μ.real (f ⁻¹' E) := congrArg μ.real hEq
    _ = _ := congrArg ENNReal.toReal (hMap.measure_preimage hE.nullMeasurableSet)

end

end ProphetSecretary.Statistics.Calibration
