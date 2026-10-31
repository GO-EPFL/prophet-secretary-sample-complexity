import ProphetSecretary.Limiting.BoundaryClippedIdentities
import ProphetSecretary.Limiting.CountablePositiveCapSelection
import ProphetSecretary.Limiting.CountableIndividualCapGain
import ProphetSecretary.Limiting.CountableCanonicalOptimizer
import ProphetSecretary.Limiting.CountableCanonicalReach

/-!
# The strict-reach contradiction for one individual carrying all excess

The clipped canonical optimizer accepts the cap and selects the excess-bearing
individual with positive probability. Its strict reach gap is therefore
positive. The actual causal lift recovers e q_i while preserving the clipped
payoff identity R_cap+e T=C, contradicting reward-only optimality of the
normalized original instance.
-/

open MeasureTheory Set Filter
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

lemma reward_critical_singleExcess_contradiction (B : CountableInstance) (hZero : B.terminal=0)
    (hM : B.expectedMaximum=1) (hV : B.optimalScalarValue 1 0=optimalCompetitiveRatio)
    (K : ℝ≥0) (hK : 0<K) (hKC : (K:ℝ)=optimalCompetitiveRatio) (j : ℕ)
    (hCloud : B.intensity (Ioi (K:ℝ))=0) (hSingle : B.individualCapExcess K j=B.totalCapExcess K) : False := by
  rcases B.boundary_clipped_identities hZero hM hV K hK hKC with ⟨_hBounds,he,hNew,_hSum,_hMax⟩
  let Q := B.capAt hZero K hK
  let e := B.totalCapExcess K
  have hQZero : Q.terminal=0 := rfl
  let π := Q.valuePolicy zero_lt_one he
  have hE : 0<B.individualCapExcess K j := by rw [hSingle];exact he
  have hValue : Q.optimalScalarValue 1 e≤(K:ℝ) := hNew.le.trans_eq hKC.symm
  have hSel : 0<π.individualSelectionProbability j := B.capAt_valuePolicy_selection_positive hZero K hK he j hValue hE
  have hReach := Q.valuePolicy_strict_individual_reach hQZero zero_lt_one he j
  have hGap : 0<π.individualReachProbability j-π.expectedDuration :=
    (div_pos (sq_pos_of_pos hSel) (by norm_num : (0:ℝ)<2)).trans_le hReach
  have hAccept := Q.valuePolicy_accepts_individual_cap hQZero zero_lt_one he j (K:ℝ) (by simpa only [one_mul] using hValue)
  let σ := RandomizedCountablePolicy.individualCapPullback hZero K hK hCloud π
  have hGain : π.expectedReward+π.individualReachProbability j*e≤σ.expectedReward := by
    have h := RandomizedCountablePolicy.individualCapPullback_expectedReward_gain hZero K hK hCloud π j hAccept
    rw [hSingle] at h
    exact h
  have hOptimal : π.expectedReward+e*π.expectedDuration=optimalCompetitiveRatio := by
    have h := Q.valuePolicy_optimal hQZero zero_lt_one he
    rw [hNew] at h
    simpa only [RandomizedCountablePolicy.scalarObjective,one_mul] using h
  have hUpper : σ.expectedReward≤optimalCompetitiveRatio := by
    have h := B.scalarObjective_le_value σ 1 0
    rw [hV] at h
    simpa only [RandomizedCountablePolicy.scalarObjective,one_mul,zero_mul,add_zero] using h
  have hStrict : 0<e*(π.individualReachProbability j-π.expectedDuration) := mul_pos he hGap
  nlinarith only [hGain,hOptimal,hUpper,hStrict]

end ProphetSecretary.Limiting.CountableInstance
