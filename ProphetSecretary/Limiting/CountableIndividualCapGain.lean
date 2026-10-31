import ProphetSecretary.Limiting.CountableIndividualCapTransport
import ProphetSecretary.Limiting.CountableReachedTail
import ProphetSecretary.Limiting.CountableCapSelection

/-!
# Recovering an individual's excess after capping its observations

A reached value above K displays K and is accepted by the capped rule. The
actual selected reward therefore recovers that individual's excess; all other
value changes can only improve reward. Reach-value factorization then yields
the exact lower gain q_i E[(X_i-K)+]. No anonymous future marks enter a callback.
-/

open MeasureTheory Set Filter
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance
variable {Seed : Type*}

lemma CountableRule.individual_cap_gain (π : CountableRule Seed) (K : ℝ≥0)
    (v : CompleteWorld Seed) (i : ℕ)
    (hFirst : FirstAcceptance.HasFirstIfAccepted (π.pullbackIndividualValues (Model.capValue K)).codeAccepted codeTime v)
    (hClock : Set.InjOn (fun c : Candidate => (candidatePoint v c).1) {c | candidatePresent v c})
    (ht : v.2.2.1 i∈Icc (0:ℝ) 1)
    (hAccept : v.2.2.1 i≤π.realizedDuration (mapIndividualWorld (Model.capValue K) v) →
      Model.capValue K (v.2.1 i)=(K:ℝ) → π.candidateAction (mapIndividualWorld (Model.capValue K) v) (Sum.inl i)=true) :
    π.realizedReward 0 (mapIndividualWorld (Model.capValue K) v)+
      (if v.2.2.1 i≤(π.pullbackIndividualValues (Model.capValue K)).realizedDuration v then Model.tailValue K (v.2.1 i) else 0)≤
      (π.pullbackIndividualValues (Model.capValue K)).realizedReward 0 v := by
  have hMono := π.pullbackIndividualValues_reward_le (Model.capValue K) 0 v (fun j => min_le_left _ _)
  by_cases hReach : v.2.2.1 i≤(π.pullbackIndividualValues (Model.capValue K)).realizedDuration v
  · by_cases hXi : (K:ℝ)≤v.2.1 i
    · have hCap : Model.capValue K (v.2.1 i)=(K:ℝ) := min_eq_right hXi
      have hR : v.2.2.1 i≤π.realizedDuration (mapIndividualWorld (Model.capValue K) v) := by
        rwa [π.pullbackIndividualValues_duration] at hReach
      have hA : (π.pullbackIndividualValues (Model.capValue K)).candidateAction v (Sum.inl i)=true :=
        (π.pullbackIndividualValues_candidateAction (Model.capValue K) v (Sum.inl i)).trans (hAccept hR hCap)
      have hCode : (π.pullbackIndividualValues (Model.capValue K)).codeAccepted v (candidateEnumeration (Sum.inl i)) := by
        refine ⟨individual_candidate_present v i,?_,?_⟩
        · rwa [codeTime_individual]
        · simpa only [Equiv.symm_apply_apply] using hA
      have hSel := (π.pullbackIndividualValues (Model.capValue K)).selectsIndividual_of_reached_accepted i v hFirst hClock hReach hCode
      have hSelCap := (π.pullbackIndividualValues_earliest (Model.capValue K) v (candidateEnumeration (Sum.inl i))).mp hSel
      have hOld : (π.pullbackIndividualValues (Model.capValue K)).realizedReward 0 v=v.2.1 i := by
        change FirstAcceptance.reward 0 _ codeTime codeValue v=_
        rw [FirstAcceptance.reward_of_earliest 0 hSel]
        change (codePoint v (candidateEnumeration (Sum.inl i))).2=_
        rw [individual_candidate_point]
      have hNew : π.realizedReward 0 (mapIndividualWorld (Model.capValue K) v)=(K:ℝ) := by
        change FirstAcceptance.reward 0 _ codeTime codeValue (mapIndividualWorld (Model.capValue K) v)=_
        rw [FirstAcceptance.reward_of_earliest 0 hSelCap]
        change (codePoint (mapIndividualWorld (Model.capValue K) v) (candidateEnumeration (Sum.inl i))).2=_
        rw [individual_candidate_point]
        exact hCap
      rw [hOld,hNew,if_pos hReach,Model.tailValue,max_eq_left (sub_nonneg.mpr hXi)]
      linarith
    · have hTail : Model.tailValue K (v.2.1 i)=0 := max_eq_right (sub_nonpos.mpr (lt_of_not_ge hXi).le)
      rwa [if_pos hReach,hTail,add_zero]
  · rwa [if_neg hReach,add_zero]

end ProphetSecretary.Limiting.CountableInstance

namespace ProphetSecretary.Limiting.RandomizedCountablePolicy
open CountableInstance
variable {B : CountableInstance}

theorem individualCapPullback_expectedReward_gain (hZero : B.terminal=0) (K : ℝ≥0) (hK : 0<K)
    (hTail : B.intensity (Ioi (K:ℝ))=0) (π : RandomizedCountablePolicy (B.capAt hZero K hK)) (i : ℕ)
    (hAccept : ∀ᵐ v ∂(B.capAt hZero K hK).completeWorldLaw π.seedLaw,
      v.2.2.1 i≤π.rule.realizedDuration v → v.2.1 i=(K:ℝ) → π.rule.candidateAction v (Sum.inl i)=true) :
    π.expectedReward+π.individualReachProbability i*B.individualCapExcess K i≤
      (individualCapPullback hZero K hK hTail π).expectedReward := by
  let σ := individualCapPullback hZero K hK hTail π
  let μ := B.completeWorldLaw π.seedLaw
  have hMP := B.capAt_completeWorld_measurePreserving hZero K hK hTail π.seedLaw
  have hCapI : Integrable (fun v => π.rule.realizedReward 0 (mapIndividualWorld (Model.capValue K) v)) μ :=
    hMP.integrable_comp_of_integrable π.integrable_reward
  have hTailFactor := σ.rule.reachedCapExcess_integrable_and_integral σ.measurable_rule B σ.seedLaw σ.admissible i K
  have hTailI : Integrable (fun v : CompleteWorld π.Seed => if v.2.2.1 i≤σ.rule.realizedDuration v then Model.tailValue K (v.2.1 i) else 0) μ := hTailFactor.1
  have hReachedMean : (∫ v : CompleteWorld π.Seed, (if v.2.2.1 i≤σ.rule.realizedDuration v then Model.tailValue K (v.2.1 i) else 0) ∂μ)=
      σ.individualReachProbability i*B.individualCapExcess K i := hTailFactor.2
  have hOldI : Integrable (σ.rule.realizedReward 0) μ := by
    change Integrable (σ.rule.realizedReward 0) (B.completeWorldLaw σ.seedLaw)
    simpa only [hZero,NNReal.coe_zero] using σ.integrable_reward
  have hPoint : ∀ᵐ v ∂μ,
      π.rule.realizedReward 0 (mapIndividualWorld (Model.capValue K) v)+
        (if v.2.2.1 i≤σ.rule.realizedDuration v then Model.tailValue K (v.2.1 i) else 0)≤σ.rule.realizedReward 0 v := by
    filter_upwards [σ.admissible,B.present_candidate_times_injective σ.seedLaw,
      B.present_candidate_times_mem_Ioo σ.seedLaw,hMP.quasiMeasurePreserving.ae hAccept] with v hF hC hT hA
    have ht := hT (Sum.inl i) trivial
    exact π.rule.individual_cap_gain K v i hF hC ⟨ht.1.le,ht.2.le⟩ hA
  have hInt := integral_mono_ae (hCapI.add hTailI) hOldI hPoint
  change (∫ v, π.rule.realizedReward 0 (mapIndividualWorld (Model.capValue K) v)+
    (if v.2.2.1 i≤σ.rule.realizedDuration v then Model.tailValue K (v.2.1 i) else 0) ∂μ)≤
      ∫ v, σ.rule.realizedReward 0 v ∂μ at hInt
  have hMeanCap : (∫ v, π.rule.realizedReward 0 (mapIndividualWorld (Model.capValue K) v) ∂μ)=π.expectedReward :=
    hMP.hasLaw.integral_comp (π.rule.measurable_realizedReward π.measurable_rule 0).aestronglyMeasurable
  have hMeanOld : (∫ v, σ.rule.realizedReward 0 v ∂μ)=σ.expectedReward := by
    change (∫ v, σ.rule.realizedReward 0 v ∂μ)=∫ v, σ.rule.realizedReward (B.terminal:ℝ) v ∂μ
    rw [hZero,NNReal.coe_zero]
  rw [integral_add (f:=fun v => π.rule.realizedReward 0 (mapIndividualWorld (Model.capValue K) v))
      (g:=fun v => if v.2.2.1 i≤σ.rule.realizedDuration v then Model.tailValue K (v.2.1 i) else 0)
      hCapI hTailI,hMeanCap,hReachedMean,hMeanOld] at hInt
  have hQ : σ.individualReachProbability i=π.individualReachProbability i :=
    individualCapPullback_individualReachProbability hZero K hK hTail π i
  rw [hQ] at hInt
  exact hInt

end ProphetSecretary.Limiting.RandomizedCountablePolicy
