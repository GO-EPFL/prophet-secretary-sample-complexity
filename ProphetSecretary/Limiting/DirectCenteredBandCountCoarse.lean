import ProphetSecretary.Limiting.DirectScheduledBandScoreL2
import ProphetSecretary.Limiting.DirectScheduledMeasurableBandCoarse
import ProphetSecretary.Probability.L2BoundedPayoff

/-!
# Literal centered finite-count joint expectations

The complete zero-atom score and the centered total virtual band count have
vanishing squared difference on the original product offer vector. A bounded
payoff may depend on all observations and on an arbitrary independent policy
seed. Cauchy--Schwarz therefore transfers its joint expectation uniformly,
without an independence assumption between the score error and the payoff.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

 theorem directScheduled_score_count_boundedPayoff_difference_tendsto
    (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    (π : ∀ m, RandomizedPolicy (m+B.directVirtualCount hZero m))
    (G : ∀ m, (π m).World → ℝ)
    (hG : ∀ m, AEStronglyMeasurable (G m) ((B.directFiniteApproximation hZero m).worldLaw (π m).seedLaw))
    {D : ℝ} (hD : 0≤D)
    (hBound : ∀ m, ∀ᵐ ω ∂(B.directFiniteApproximation hZero m).worldLaw (π m).seedLaw, |G m ω|≤D) :
    Tendsto (fun m =>
      (∫ ω : (π m).World, completeScore (B.directScheduledCloudScore hZero S m) ω.1*G m ω
        ∂(B.directFiniteApproximation hZero m).worldLaw (π m).seedLaw)-
      (∫ ω : (π m).World, (countIn S (fun j => ω.1 (j.natAdd m))-B.intensity.real S)*G m ω
        ∂(B.directFiniteApproximation hZero m).worldLaw (π m).seedLaw)) atTop (𝓝 (0:ℝ)) := by
  let P := B.directFiniteApproximation hZero
  let Z := fun m (ω : (π m).World) => completeScore (B.directScheduledCloudScore hZero S m) ω.1
  let C := fun m (ω : (π m).World) => countIn S (fun j => ω.1 (j.natAdd m))-B.intensity.real S
  let E := fun m (x : Fin (m+B.directVirtualCount hZero m) → ℝ) =>
    completeScore (B.directScheduledCloudScore hZero S m) x-(countIn S (fun j => x (j.natAdd m))-B.intensity.real S)
  have hEInt (m) : Integrable (fun x => (E m x)^2) (P m).valuesLaw :=
    B.directScheduled_bandScore_count_error_integrable_sq hZero hS hb hSub m
  have hEMeas (m) : Measurable (E m) := B.directScheduled_bandScore_count_error_measurable hZero hS hb hSub m
  have hEMP (m) : MeasurePreserving (fun ω : (π m).World => ω.1) ((P m).worldLaw (π m).seedLaw) (P m).valuesLaw :=
    measurePreserving_fst
  have hELp (m) : MemLp (fun ω : (π m).World => E m ω.1) 2 ((P m).worldLaw (π m).seedLaw) :=
    ((memLp_two_iff_integrable_sq (hEMeas m).aestronglyMeasurable).mpr (hEInt m)).comp_measurePreserving (hEMP m)
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  have hZLp (m) : MemLp (Z m) 2 ((P m).worldLaw (π m).seedLaw) := by
    have hProps := B.directScheduledCloudScore_properties hZero hS hS0 m
    have hInt := completeScore_integrable_pow (P m).law (B.directScheduledCloudScore hZero S m) hProps.1
      (fun j => Eventually.of_forall (hProps.2.1 j)) 2
    exact ((memLp_two_iff_integrable_sq (measurable_completeScore hProps.1).aestronglyMeasurable).mpr hInt).comp_measurePreserving (hEMP m)
  have hCLp (m) : MemLp (C m) 2 ((P m).worldLaw (π m).seedLaw) := by
    have hEq : (Z m-(fun ω : (π m).World => E m ω.1)) =ᵐ[(P m).worldLaw (π m).seedLaw] C m :=
      Eventually.of_forall (fun ω => by dsimp only [Pi.sub_apply,Z,E,C];ring)
    exact (memLp_congr_ae hEq).mp ((hZLp m).sub (hELp m))
  have hRateData := B.directScheduled_bandScore_count_error_tendsto hZero hS hb hSub
  have hRate : Tendsto (fun m => ∫ ω : (π m).World, (Z m ω-C m ω)^2 ∂(P m).worldLaw (π m).seedLaw)
      atTop (𝓝 (0:ℝ)) := by
    apply hRateData.congr
    intro m
    exact ((hEMP m).hasLaw.integral_comp (hEInt m).aestronglyMeasurable).symm
  have hUpper : Tendsto (fun m => D*Real.sqrt (∫ ω : (π m).World, (Z m ω-C m ω)^2
      ∂(P m).worldLaw (π m).seedLaw)) atTop (𝓝 (0:ℝ)) := by
    simpa only [Function.comp_apply,Real.sqrt_zero,mul_zero] using
      ((Real.continuous_sqrt.tendsto 0).comp hRate).const_mul D
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  simp only [sub_zero,Real.norm_eq_abs]
  exact squeeze_zero (fun _ => abs_nonneg _)
    (fun m => score_payoff_difference_le_L2_ae ((P m).worldLaw (π m).seedLaw) (Z m) (C m) (G m)
      (hZLp m) (hCLp m) (hG m) hD (hBound m) (le_refl _)) hUpper

 theorem directScheduled_coarse_centeredBandCount_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    {K : ℕ} (π : RandomizedHybridPolicy K) (d : ℝ) (hd : (B.terminal:ℝ)<d) :
    let γ := fun m => directCoarsePolicy m (B.directVirtualCount hZero m) π d
    Tendsto (fun m => ∫ ω : (γ m).World, (countIn S (fun j => ω.1 (j.natAdd m))-B.intensity.real S)*
      (γ m).realizedReward ω ∂(B.directFiniteApproximation hZero m).worldLaw (γ m).seedLaw) atTop
      (𝓝 (∫ v, B.bandScore S v*(π.extendToCountable B hd).rule.realizedReward B.terminal v ∂B.completeWorldLaw π.seedLaw)) ∧
    Tendsto (fun m => ∫ ω : (γ m).World, (countIn S (fun j => ω.1 (j.natAdd m))-B.intensity.real S)*
      (γ m).realizedDuration ω ∂(B.directFiniteApproximation hZero m).worldLaw (γ m).seedLaw) atTop
      (𝓝 (∫ v, B.bandScore S v*(π.extendToCountable B hd).rule.realizedDuration v ∂B.completeWorldLaw π.seedLaw)) := by
  let γ := fun m => directCoarsePolicy m (B.directVirtualCount hZero m) π d
  have hRanges (m) := finite_policy_outcome_ranges (γ m) (B.directFiniteApproximation hZero m) B.cap
    (B.directFiniteApproximation_bounded hZero m)
  have hRD := B.directScheduled_score_count_boundedPayoff_difference_tendsto hZero hS hb hSub γ
    (fun m => (γ m).realizedReward) (fun m => (γ m).measurable_realizedReward.aestronglyMeasurable) B.cap.property
    (fun m => (hRanges m).mono (fun _ hω => by rw [abs_of_nonneg hω.1.1];exact hω.1.2))
  have hTD := B.directScheduled_score_count_boundedPayoff_difference_tendsto hZero hS hb hSub γ
    (fun m => (γ m).realizedDuration) (fun m => (γ m).measurable_realizedDuration.aestronglyMeasurable) (D := 1) (by norm_num)
    (fun m => (hRanges m).mono (fun _ hω => by rw [abs_of_nonneg hω.2.1];exact hω.2.2))
  have h := B.directScheduled_coarse_measurableBand_score_tendsto hZero hS hb hSub π d hd
  constructor
  · simpa only [RandomizedPolicy.expectedRewardScore,γ,sub_sub_cancel,sub_zero] using h.1.sub hRD
  · simpa only [RandomizedPolicy.expectedDurationScore,γ,sub_sub_cancel,sub_zero] using h.2.sub hTD
end ProphetSecretary.Limiting.CountableInstance
