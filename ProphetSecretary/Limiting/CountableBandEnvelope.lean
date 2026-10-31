import ProphetSecretary.Limiting.CountableBandResponses
import ProphetSecretary.Limiting.CountableScoreStability
import ProphetSecretary.Limiting.CountableCanonicalLimit
import ProphetSecretary.Analysis.StableEnvelope

/-!
# The band-likelihood envelope in the full limiting model

A fixed base-optimal policy determines the derivative. The proof uses an
actual common unrestricted policy class and the uniform quadratic likelihood
remainder; the centered complete count remains an analytical random variable.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal

namespace ProphetSecretary.Limiting
open CountableInstance

lemma CountableInstance.integral_abs_bandScore_le (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∫ v, |B.bandScore S v| ∂B.completeWorldLaw ν)≤2*B.intensity.real S := by
  have hLaw := B.completeBandCount_hasLaw hS hb hSub ν
  have hAbs := hLaw.integral_comp ((ProphetSecretary.Probability.measurable_poissonCenteredScore (B.bandRate S)).norm).aestronglyMeasurable
  simp only [Real.norm_eq_abs,Function.comp_apply] at hAbs
  change (∫ v, |ProphetSecretary.Probability.poissonCenteredScore (B.bandRate S) (completeBandCount S v)| ∂B.completeWorldLaw ν)≤_
  rw [hAbs]
  calc
    _ ≤ ∫ n : ℕ, (n : ℝ)+(B.bandRate S : ℝ) ∂ProbabilityTheory.poissonMeasure (B.bandRate S) := by
      apply integral_mono (ProphetSecretary.Probability.integrable_poissonCenteredScore (B.bandRate S)).abs
        ((poisson_first_integrable (B.bandRate S)).add (integrable_const _))
      intro n
      change |(n : ℝ)-(B.bandRate S : ℝ)|≤(n : ℝ)+(B.bandRate S : ℝ)
      simpa only [abs_of_nonneg (show (0 : ℝ)≤(n : ℝ) from Nat.cast_nonneg n),
        abs_of_nonneg (show (0 : ℝ)≤(B.bandRate S : ℝ) from (B.bandRate S).property)] using
        abs_sub (n : ℝ) (B.bandRate S : ℝ)
    _ = _ := by
      rw [integral_add (poisson_first_integrable (B.bandRate S)) (integrable_const _),integral_poisson_first,integral_const]
      simp only [probReal_univ,one_smul,bandRate_coe]
      ring

lemma RandomizedCountablePolicy.scalarBandLikelihoodDerivative_bound {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    |π.scalarBandLikelihoodDerivative S w c|≤2*(w*(B.cap : ℝ)+c)*B.intensity.real S := by
  have hNorm : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw,
      ‖π.scalarPayoff w c v*B.bandScore S v‖≤(w*(B.cap : ℝ)+c)*|B.bandScore S v| := by
    filter_upwards [π.scalarPayoff_bounded hw hc] with v hv
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hv.1]
    exact mul_le_mul_of_nonneg_right hv.2 (abs_nonneg _)
  have h := norm_integral_le_of_norm_le ((B.integrable_bandScore hS hb hSub π.seedLaw).abs.const_mul (w*(B.cap : ℝ)+c)) hNorm
  rw [integral_const_mul] at h
  change |π.scalarBandLikelihoodDerivative S w c|≤_
  calc
    _ ≤ (w*(B.cap : ℝ)+c)*(∫ v, |B.bandScore S v| ∂B.completeWorldLaw π.seedLaw) := h
    _ ≤ (w*(B.cap : ℝ)+c)*(2*B.intensity.real S) :=
      mul_le_mul_of_nonneg_left (B.integral_abs_bandScore_le hS hb hSub π.seedLaw) (by positivity)
    _ = _ := by ring

lemma RandomizedCountablePolicy.scalarBandLikelihoodDerivative_difference_le {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    |π.scalarBandLikelihoodDerivative S w c-(B.valuePolicy hw hc).scalarBandLikelihoodDerivative S w c|≤
      (w+c)*Real.sqrt (2*B.intensity.real S*((B.cap : ℝ)+1)*π.expectedValueOutcomeError w c) := by
  let π₀ := B.valuePolicy hw hc
  let F := fun v : CompleteWorld Unit => π₀.scalarPayoff w c v*B.bandScore S v
  have hF : Measurable F := (π₀.measurable_scalarPayoff w c).mul (B.measurable_bandScore hS)
  have hFI : Integrable F (B.completeWorldLaw (Measure.dirac ())) := π₀.integrable_scalarBandLikelihood hS hb hSub hw.le hc.le
  have hSeed := B.eraseCompleteSeed_measurePreserving π.seedLaw
  have hMean := hSeed.hasLaw.integral_comp hF.aestronglyMeasurable
  change (∫ v, F (eraseCompleteSeed v) ∂B.completeWorldLaw π.seedLaw)=π₀.scalarBandLikelihoodDerivative S w c at hMean
  have hOldI := π.integrable_scalarBandLikelihood hS hb hSub hw.le hc.le
  have hBaseI : Integrable (fun v => F (eraseCompleteSeed v)) (B.completeWorldLaw π.seedLaw) := hSeed.integrable_comp_of_integrable hFI
  have hProd := π.score_coupledDifferences_integrable hw.le hc.le (B.bandScore S) (B.bandScore_memLp_two hS hb hSub π.seedLaw)
  have hDiff : π.scalarBandLikelihoodDerivative S w c-π₀.scalarBandLikelihoodDerivative S w c=
      w*(∫ v, B.bandScore S v*π.coupledRewardDifference w c v ∂B.completeWorldLaw π.seedLaw)+
      c*(∫ v, B.bandScore S v*π.coupledDurationDifference w c v ∂B.completeWorldLaw π.seedLaw) := by
    rw [← hMean]
    change (∫ v, π.scalarPayoff w c v*B.bandScore S v ∂B.completeWorldLaw π.seedLaw)-_=_
    rw [← integral_sub hOldI hBaseI,← integral_const_mul,← integral_const_mul,← integral_add (hProd.1.const_mul w) (hProd.2.const_mul c)]
    apply integral_congr_ae
    exact Eventually.of_forall (fun v => by
      dsimp only [scalarBandLikelihoodDerivative,RandomizedCountablePolicy.scalarPayoff,F,π₀,
        RandomizedCountablePolicy.coupledRewardDifference,RandomizedCountablePolicy.coupledDurationDifference,
        CountableInstance.valuePolicy,eraseCompleteSeed,bandScore,completeBandCount]
      ring)
  have hStab := π.score_stability hw.le hc.le (B.bandScore S) (B.bandScore_memLp_two hS hb hSub π.seedLaw)
    (B.bandScore_information hS hb hSub π.seedLaw).le le_rfl
  rw [hDiff]
  calc
    _ ≤ |w*(∫ v, B.bandScore S v*π.coupledRewardDifference w c v ∂B.completeWorldLaw π.seedLaw)|+
      |c*(∫ v, B.bandScore S v*π.coupledDurationDifference w c v ∂B.completeWorldLaw π.seedLaw)| := abs_add_le _ _
    _ ≤ (w+c)*((|∫ v, B.bandScore S v*π.coupledRewardDifference w c v ∂B.completeWorldLaw π.seedLaw|)+
      |∫ v, B.bandScore S v*π.coupledDurationDifference w c v ∂B.completeWorldLaw π.seedLaw|) := by
      rw [abs_mul,abs_mul,abs_of_pos hw,abs_of_pos hc]
      nlinarith [abs_nonneg (∫ v, B.bandScore S v*π.coupledRewardDifference w c v ∂B.completeWorldLaw π.seedLaw),
        abs_nonneg (∫ v, B.bandScore S v*π.coupledDurationDifference w c v ∂B.completeWorldLaw π.seedLaw)]
    _ ≤ _ := mul_le_mul_of_nonneg_left hStab (add_nonneg hw.le hc.le)

/-- The Poisson-band likelihood part of `lem:envelopes`, with the affected
marks bounded away from the reserve. -/
theorem CountableInstance.hasDerivAt_optimalScalarValue_bandLikelihoodPath
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b) :
    HasDerivAt (fun θ => (B.bandLikelihoodPath S θ).optimalScalarValue w c)
      ((B.valuePolicy hw hc).scalarBandLikelihoodDerivative S w c) 0 := by
  let π₀ := B.valuePolicy hw hc
  let J := fun θ (π : RandomizedCountablePolicy B) => (π.bandLikelihoodPolicy hS hb hSub θ).scalarObjective w c
  let D := fun π : RandomizedCountablePolicy B => π.scalarBandLikelihoodDerivative S w c
  have hZeroJ (π : RandomizedCountablePolicy B) : J 0 π=π.scalarObjective w c := by
    have h := π.bandLikelihoodPolicy_scalarObjective_taylor hS hb hSub hw.le hc.le (by norm_num : |(0 : ℝ)|≤1/4)
    have hEq := abs_nonpos_iff.mp (show |J 0 π-π.scalarObjective w c|≤0 by simpa only [zero_mul,mul_zero,zero_pow (by decide : (2 : ℕ)≠0),sub_zero] using h)
    exact sub_eq_zero.mp hEq
  have hBase : ∀ π, J 0 π≤J 0 π₀ := by
    intro π
    rw [hZeroJ,hZeroJ]
    exact (B.scalarObjective_le_value π w c).trans_eq (B.valuePolicy_optimal hZero hw hc).symm
  have hD : ∀ π, |D π|≤2*(w*(B.cap : ℝ)+c)*B.intensity.real S := fun π =>
    π.scalarBandLikelihoodDerivative_bound hS hb hSub hw.le hc.le
  have hTaylor : ∀ θ, |θ|≤1/4 → ∀ π,
      |J θ π-J 0 π-θ*D π|≤(2*(w*(B.cap : ℝ)+c)*B.intensity.real S)*θ^2 := by
    intro θ hθ π
    rw [hZeroJ]
    exact (π.bandLikelihoodPolicy_scalarObjective_taylor hS hb hSub hw.le hc.le hθ).trans_eq (by ring)
  obtain ⟨Ω,_,hMono,_,hLimit,hError⟩ := B.outcome_stability hZero hw hc
  let K := 2*B.intensity.real S*((B.cap : ℝ)+1)
  have hK : 0≤K := by dsimp only [K]; positivity
  have hStable : ∀ ε, 0<ε → ∃ η, 0<η ∧ ∀ π, J 0 π₀-J 0 π≤η → |D π-D π₀|≤ε := by
    intro ε hε
    have hLimitK : Tendsto (fun r => (w+c)*Real.sqrt (K*Ω r)) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [Function.comp_apply,mul_zero,Real.sqrt_zero] using (Real.continuous_sqrt.continuousAt.tendsto.comp (hLimit.const_mul K)).const_mul (w+c)
    obtain ⟨η,hηSmall,hη⟩ := ((hLimitK.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
    refine ⟨η,hη,?_⟩
    intro π hNear
    have hRegret : B.optimalScalarValue w c-π.scalarObjective w c≤η := by
      rw [hZeroJ,hZeroJ,B.valuePolicy_optimal hZero hw hc] at hNear
      exact hNear
    have hBound := π.scalarBandLikelihoodDerivative_difference_le hS hb hSub hw hc
    have hMean := mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt
      (mul_le_mul_of_nonneg_left ((hError π).trans (hMono hRegret)) hK)) (add_nonneg hw.le hc.le)
    exact hBound.trans (hMean.trans hηSmall.le)
  have hDeriv := ProphetSecretary.Analysis.hasDerivAt_supremum_of_stable_payoffs J D π₀
    (show 0≤2*(w*(B.cap : ℝ)+c)*B.intensity.real S by positivity)
    (show 0≤2*(w*(B.cap : ℝ)+c)*B.intensity.real S by positivity)
    (by norm_num : (0 : ℝ)<1/4) hBase hD hTaylor hStable
  have hSup (θ : ℝ) : (B.bandLikelihoodPath S θ).optimalScalarValue w c=sSup (Set.range (J θ)) :=
    B.optimalScalarValue_eq_sSup_transport (B.bandLikelihoodPath S θ)
      (fun π => B.bandLikelihoodPath_absolutelyContinuous hS hb hSub θ π.seedLaw)
      (fun π => B.absolutelyContinuous_bandLikelihoodPath hS hb hSub θ π.seedLaw) w c
  have hFunctions : (fun θ => sSup (Set.range (J θ)))=(fun θ => (B.bandLikelihoodPath S θ).optimalScalarValue w c) :=
    funext (fun θ => (hSup θ).symm)
  rw [hFunctions] at hDeriv
  exact hDeriv

end ProphetSecretary.Limiting
