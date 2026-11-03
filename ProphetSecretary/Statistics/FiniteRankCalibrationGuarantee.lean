import ProphetSecretary.Statistics.ReportedRankGuarantee
import ProphetSecretary.Statistics.RoundedKeyCoinTransfer
import ProphetSecretary.Statistics.FiniteRankCalibratedLearner

/-!
# Transfer from the reported selector to actual finite bits

The rank implementation with uniform validation permutations matches the
reported selector exactly. Replacing the keys and the independent coin
by finite grids then gives the stated additive error on reward and reach.
-/

open MeasureTheory Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {TSeed PSeed : Type} [MeasurableSpace TSeed] [MeasurableSpace PSeed] [NeZero m]

theorem finiteRankCalibratedLearner_transfer (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1)
    (b c : ℕ) (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    (mu : ℝ) {zlo zhi : ℝ} (h0 : 0≤zlo) (hz : zlo≤zhi)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    let f := uniformGridRound (2^b) (by positivity)
    let hf := measurable_uniformGridRound (2^b) (by positivity)
    let est := clockRoundedEstimate f policyEstimate
    let he := measurable_clockRoundedEstimate hf policyEstimate hC
    let report := terminalClockReport f
    let A := reportedOfflinePrepare (J := J) report mu zlo zhi targetEstimate est
    let hA := measurable_reportedOfflinePrepare (J := J) report (measurable_terminalClockReport hf)
      mu zlo zhi targetEstimate est hT he
    let L := selectorLearner νT νP zlo zhi est A hA he
    let R := finiteRankCalibratedLearner (J := J) b c νT νP mu zlo zhi targetEstimate policyEstimate hT hC
    let e := (m : ℝ)*((n : ℝ)*((n : ℝ)-1))/(2*((2^b : ℕ) : ℝ))+1/((2^c : ℕ) : ℝ)
    L.expectedReward P-e≤R.expectedReward P ∧
      ∀ i : Fin n, L.reachProbability P i-e≤R.reachProbability P i := by
  let N := 2^b
  let Q := 2^c
  have hN : 0<N := by dsimp [N]; positivity
  have hQ : 0<Q := by dsimp [Q]; positivity
  let f := uniformGridRound N hN
  have hf : Measurable f := measurable_uniformGridRound N hN
  let times := mappedSortedClockLaw n f hf
  let est := clockRoundedEstimate f policyEstimate
  let he := measurable_clockRoundedEstimate hf policyEstimate hC
  let report := terminalClockReport f
  let A := reportedOfflinePrepare (J := J) report mu zlo zhi targetEstimate est
  let hA := measurable_reportedOfflinePrepare (J := J) report (measurable_terminalClockReport hf)
    mu zlo zhi targetEstimate est hT he
  let L := selectorLearner νT νP zlo zhi est A hA he
  let R := finiteRankCalibratedLearner (J := J) b c νT νP mu zlo zhi targetEstimate policyEstimate hT hC
  let e := (m : ℝ)*((n : ℝ)*((n : ℝ)-1))/(2*(N : ℝ))+1/(Q : ℝ)
  have hF (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) : f t∈Icc (0 : ℝ) t :=
    let h := uniformGridRound_bounds N hN ht
    ⟨h.1,h.2.1⟩
  have hI := idealRankCalibratedLearner_reported_reward_eq (J := J) P νT νP hf hF
    mu h0 hz targetEstimate policyEstimate hT hC (P.integrable_maximum_of_bounded hcap)
  have hTransfer := roundedKeysCoin_expectedReward (J := J) P νT νP times hN hQ mu zlo zhi
    targetEstimate policyEstimate hT hC hcap
  have hBit := finiteRankCalibratedLearner_reward_eq (J := J) b c νT νP mu zlo zhi
    targetEstimate policyEstimate hT hC P
  change L.expectedReward P-e≤R.expectedReward P ∧
    ∀ i : Fin n,L.reachProbability P i-e≤R.reachProbability P i
  constructor
  · exact (congrArg (fun t : ℝ => t-e) hI.symm).le.trans (hTransfer.trans hBit.symm.le)
  · intro i
    have hI := idealRankCalibratedLearner_reported_reach_eq (J := J) P νT νP hf hF
      mu h0 hz targetEstimate policyEstimate hT hC i
    have hTransfer := roundedKeysCoin_reachProbability (J := J) P νT νP times hN hQ mu zlo zhi
      targetEstimate policyEstimate hT hC i
    have hBit := finiteRankCalibratedLearner_reach_eq (J := J) b c νT νP mu zlo zhi
      targetEstimate policyEstimate hT hC P i
    exact (congrArg (fun t : ℝ => t-e) hI.symm).le.trans (hTransfer.trans hBit.symm.le)

end ProphetSecretary.Statistics.Calibration
