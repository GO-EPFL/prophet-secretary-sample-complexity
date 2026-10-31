import ProphetSecretary.Limiting.CountableLikelihoodCrossCoefficients

/-!
# The fixed-base individual-likelihood target derivative

The callbacks and seed of the base canonical optimizer remain fixed along the
actual likelihood path. Scalar stationarity is derived from the reoptimized
value separately. Their combination yields the derivative of R−T−C(M−1).
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

noncomputable def individualFixedTargetDifference (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (i : ℕ) (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x|≤1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) (θ : ℝ) : ℝ :=
  ((B.valuePolicy hw hc).individualLikelihoodPolicy i h hh hb hm θ).expectedReward-
    ((B.valuePolicy hw hc).individualLikelihoodPolicy i h hh hb hm θ).expectedDuration-
    optimalCompetitiveRatio*((B.individualLikelihoodPath i h hh hb hm θ).expectedMaximum-1)

theorem hasDerivAt_individualFixedTargetDifference (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hSum : w+c=1) (hCritical : B.IsCritical w c)
    (i : ℕ) (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x|≤1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) :
    HasDerivAt (B.individualFixedTargetDifference hw hc i h hh hb hm)
      (-((B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i 0 1 h)/w) 0 := by
  let π0 := B.valuePolicy hw hc
  have hR : HasDerivAt (fun θ => (π0.individualLikelihoodPolicy i h hh hb hm θ).expectedReward)
      (π0.scalarIndividualLikelihoodDerivative i 1 0 h) 0 := by
    simpa only [RandomizedCountablePolicy.scalarObjective,one_mul,zero_mul,add_zero] using
      π0.hasDerivAt_scalarObjective_individualLikelihoodPolicy i h hh hb hm 1 0
  have hT : HasDerivAt (fun θ => (π0.individualLikelihoodPolicy i h hh hb hm θ).expectedDuration)
      (π0.scalarIndividualLikelihoodDerivative i 0 1 h) 0 := by
    simpa only [RandomizedCountablePolicy.scalarObjective,zero_mul,one_mul,zero_add] using
      π0.hasDerivAt_scalarObjective_individualLikelihoodPolicy i h hh hb hm 0 1
  have hM := B.hasDerivAt_expectedMaximum_individualLikelihoodPath i h hh hb hm
  have hStat : w*π0.scalarIndividualLikelihoodDerivative i 1 0 h+
      c*π0.scalarIndividualLikelihoodDerivative i 0 1 h=
      optimalCompetitiveRatio*w*B.prophetIndividualLikelihoodDerivative i h := by
    rw [←π0.scalarIndividualLikelihoodDerivative_weights i h hh hb w c]
    exact B.critical_individual_likelihood_stationarity hw hc hCritical i h hh hb hm
  have hCross := normalized_stationarity_cross hw.ne' hSum hStat
  have hDeriv := (hR.sub hT).sub ((hM.sub_const 1).const_mul optimalCompetitiveRatio)
  rw [hCross] at hDeriv
  exact hDeriv

end ProphetSecretary.Limiting.CountableInstance
