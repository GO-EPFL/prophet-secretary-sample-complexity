import ProphetSecretary.Limiting.DirectCoarseMeasurableBandScore
import ProphetSecretary.Limiting.DirectScheduledCloudMaximumScore

/-!
# Coarse comparisons for the actual direct schedule

All rarity, intensity and information conditions are discharged by the
prescribed schedule. Every measurable scored set bounded away from zero is
allowed, including a set crossing the comparator's observation cutoff.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

 theorem directScheduled_coarse_payoffs_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    {K : ℕ} (π : RandomizedHybridPolicy K) (d : ℝ) (hd : (B.terminal:ℝ)<d) :
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedReward
      (B.directFiniteApproximation hZero m)) atTop (𝓝 ((π.extendToCountable B hd).expectedReward)) ∧
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedDuration
      (B.directFiniteApproximation hZero m)) atTop (𝓝 ((π.extendToCountable B hd).expectedDuration)) := by
  have h := B.directPrescribed_coarse_payoffs_tendsto hZero id (B.directVirtualCount hZero) B.markCutoff
    B.terminal_lt_markCutoff (B.directVirtualCount_positive hZero) (B.directVirtualCount_rate_le hZero)
    tendsto_id B.markCutoff_tendsto (B.directVirtualCount_square_error_tendsto hZero) π d hd
  constructor
  · exact h.1.congr (fun m => congrArg (fun P => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedReward P)
      (B.directFiniteApproximation_eq_prescribedCount hZero m).symm)
  · exact h.2.congr (fun m => congrArg (fun P => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedDuration P)
      (B.directFiniteApproximation_eq_prescribedCount hZero m).symm)

 theorem directScheduled_coarse_measurableBand_scalarScore_tendsto
    (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    {K : ℕ} (π : RandomizedHybridPolicy K) (d : ℝ) (hd : (B.terminal:ℝ)<d)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    Tendsto (fun m => w*(directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedRewardScore
      (B.directFiniteApproximation hZero m) (B.directScheduledCloudScore hZero S m)+
      c*(directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedDurationScore
      (B.directFiniteApproximation hZero m) (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 ((π.extendToCountable B hd).scalarBandLikelihoodDerivative S w c)) := by
  let A := fun m => B.finiteDirectApproximationAt m (B.markCutoff m) (B.terminal_lt_markCutoff m)
    (B.directVirtualCount hZero m) (B.directVirtualCount_positive hZero m) (B.directVirtualCount_rate_le hZero m)
  let score := fun m => B.directScheduledCloudScore hZero S m
  have hEq (m) : A m=B.directFiniteApproximation hZero m := (B.directFiniteApproximation_eq_prescribedCount hZero m).symm
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  have hProps (m) := B.directScheduledCloudScore_properties hZero hS hS0 m
  have hz (m) : ∀ j, (∫ x, score m j x ∂(A m).law j)=0 := by
    rw [hEq m]
    exact (hProps m).2.2.1
  have hInfo (m) : information (A m).law (score m)≤2*B.intensity.real S := by
    rw [hEq m]
    exact B.directScheduledCloudScore_information_le hZero hS hb hSub m
  have h := B.direct_coarse_measurableBand_scalarScore_tendsto hZero id (B.directVirtualCount hZero) B.markCutoff
    B.terminal_lt_markCutoff (B.directVirtualCount_positive hZero) (B.directVirtualCount_rate_le hZero)
    (B.directVirtualCount_probability_le_half hZero) tendsto_id B.markCutoff_tendsto
    (B.directVirtualCount_square_error_tendsto hZero) hS hS0 (B.intensity_band_finite hb hSub)
    π d hd hw hc (by positivity : 0≤2*B.intensity.real S) (fun m => (hProps m).1)
    (fun m j => Filter.Eventually.of_forall ((hProps m).2.1 j)) hz hInfo
  exact h.congr (fun m => congrArg (fun P => w*(directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedRewardScore P (score m)+
    c*(directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedDurationScore P (score m)) (hEq m))

 theorem directScheduled_coarse_measurableBand_score_tendsto
    (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    {K : ℕ} (π : RandomizedHybridPolicy K) (d : ℝ) (hd : (B.terminal:ℝ)<d) :
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedRewardScore
      (B.directFiniteApproximation hZero m) (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 (∫ v, B.bandScore S v*(π.extendToCountable B hd).rule.realizedReward B.terminal v ∂B.completeWorldLaw π.seedLaw)) ∧
    Tendsto (fun m => (directCoarsePolicy m (B.directVirtualCount hZero m) π d).expectedDurationScore
      (B.directFiniteApproximation hZero m) (B.directScheduledCloudScore hZero S m)) atTop
      (𝓝 (∫ v, B.bandScore S v*(π.extendToCountable B hd).rule.realizedDuration v ∂B.completeWorldLaw π.seedLaw)) := by
  have hR := B.directScheduled_coarse_measurableBand_scalarScore_tendsto hZero hS hb hSub π d hd
    (w := 1) (c := 0) (by norm_num) (by norm_num)
  have hT := B.directScheduled_coarse_measurableBand_scalarScore_tendsto hZero hS hb hSub π d hd
    (w := 0) (c := 1) (by norm_num) (by norm_num)
  have h := And.intro hR hT
  simp only [one_mul,zero_mul,add_zero,zero_add,RandomizedCountablePolicy.scalarBandLikelihoodDerivative,
    RandomizedCountablePolicy.scalarPayoff,mul_comm] at h
  convert h using 1 <;> rfl
end ProphetSecretary.Limiting.CountableInstance
