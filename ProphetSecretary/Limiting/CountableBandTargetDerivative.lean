import ProphetSecretary.Limiting.CountableLikelihoodCrossCoefficients

/-!
# The fixed-base Poisson-band target derivative

The actual complete-count score differentiates the reward and duration of the
fixed base policy. Reoptimized scalar stationarity then identifies the target
response with minus the duration response divided by its positive reward weight.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

noncomputable def bandFixedTargetDifference (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b) (θ : ℝ) : ℝ :=
  ((B.valuePolicy hw hc).bandLikelihoodPolicy hS hb hSub θ).expectedReward-
    ((B.valuePolicy hw hc).bandLikelihoodPolicy hS hb hSub θ).expectedDuration-
    optimalCompetitiveRatio*((B.bandLikelihoodPath S θ).expectedMaximum-1)

theorem hasDerivAt_bandFixedTargetDifference (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hSum : w+c=1) (hCritical : B.IsCritical w c)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b) :
    HasDerivAt (B.bandFixedTargetDifference hw hc hS hb hSub)
      (-((B.valuePolicy hw hc).scalarBandLikelihoodDerivative S 0 1)/w) 0 := by
  let π0 := B.valuePolicy hw hc
  have hR : HasDerivAt (fun θ => (π0.bandLikelihoodPolicy hS hb hSub θ).expectedReward)
      (π0.scalarBandLikelihoodDerivative S 1 0) 0 := by
    simpa only [RandomizedCountablePolicy.scalarObjective,one_mul,zero_mul,add_zero] using
      π0.hasDerivAt_scalarObjective_bandLikelihoodPolicy hS hb hSub (w:=1) (c:=0) (by norm_num) (by norm_num)
  have hT : HasDerivAt (fun θ => (π0.bandLikelihoodPolicy hS hb hSub θ).expectedDuration)
      (π0.scalarBandLikelihoodDerivative S 0 1) 0 := by
    simpa only [RandomizedCountablePolicy.scalarObjective,zero_mul,one_mul,zero_add] using
      π0.hasDerivAt_scalarObjective_bandLikelihoodPolicy hS hb hSub (w:=0) (c:=1) (by norm_num) (by norm_num)
  have hM := B.hasDerivAt_expectedMaximum_bandLikelihoodPath hS hb hSub
  have hStat : w*π0.scalarBandLikelihoodDerivative S 1 0+c*π0.scalarBandLikelihoodDerivative S 0 1=
      optimalCompetitiveRatio*w*B.prophetBandLikelihoodDerivative S := by
    rw [←π0.scalarBandLikelihoodDerivative_weights hS hb hSub w c]
    exact B.critical_band_likelihood_stationarity hw hc hCritical hS hb hSub
  have hCross := normalized_stationarity_cross hw.ne' hSum hStat
  have hDeriv := (hR.sub hT).sub ((hM.sub_const 1).const_mul optimalCompetitiveRatio)
  rw [hCross] at hDeriv
  exact hDeriv

end ProphetSecretary.Limiting.CountableInstance
