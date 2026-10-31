import ProphetSecretary.Limiting.CountableBandPayoff

/-!
# Fixed-policy responses to Poisson band likelihoods

The independent seed law and callbacks stay fixed. The complete band count
is used only as an analytical likelihood score.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal Topology

namespace ProphetSecretary.Limiting
open CountableInstance

lemma RandomizedCountablePolicy.bandLikelihoodPolicy_durationMean {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b) {θ : ℝ} (hθ : |θ| ≤ 1/4) :
    (π.bandLikelihoodPolicy hS hb hSub θ).expectedDuration=
      ProphetSecretary.Probability.poissonPayoffMean (B.completeWorldLaw π.seedLaw) (B.bandRate S)
        (completeBandCount S) π.rule.realizedDuration θ := by
  change (∫ v : CompleteWorld π.Seed, π.rule.realizedDuration v ∂(B.bandLikelihoodPath S θ).completeWorldLaw π.seedLaw)=_
  rw [B.bandLikelihoodPath_completeWorldLaw_numeric hS hb hSub hθ π.seedLaw]
  have hDensity : Measurable (fun v : CompleteWorld π.Seed => ENNReal.ofReal
      (ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v))) :=
    ENNReal.measurable_ofReal.comp ((measurable_of_countable
      (ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ)).comp (measurable_completeBandCount hS))
  rw [integral_withDensity_eq_integral_toReal_smul hDensity (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by
    have hPositive : 0 < 1+θ := by linarith only [(abs_le.mp hθ).1]
    have hNonnegative : 0 ≤ ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v) :=
      mul_nonneg (Real.exp_pos _).le (pow_nonneg hPositive.le _)
    change (ENNReal.ofReal (ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v))).toReal •
      π.rule.realizedDuration v=π.rule.realizedDuration v*ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v)
    rw [ENNReal.toReal_ofReal hNonnegative,smul_eq_mul,mul_comm])

theorem RandomizedCountablePolicy.hasDerivAt_scalarObjective_bandLikelihoodPolicy
    {B : CountableInstance} (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b)
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    HasDerivAt (fun θ => (π.bandLikelihoodPolicy hS hb hSub θ).scalarObjective w c)
      (π.scalarBandLikelihoodDerivative S w c) 0 := by
  have hBound : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, |π.scalarPayoff w c v|≤w*(B.cap : ℝ)+c :=
    (π.scalarPayoff_bounded hw hc).mono (fun v hv => by rw [abs_of_nonneg hv.1]; exact hv.2)
  have hd := (ProphetSecretary.Probability.poissonPayoff_derivatives (B.completeWorldLaw π.seedLaw) (B.bandRate S)
    (completeBandCount S) (measurable_completeBandCount hS) (B.completeBandCount_hasLaw hS hb hSub π.seedLaw)
    (π.scalarPayoff w c) (π.measurable_scalarPayoff w c) (show 0≤w*(B.cap : ℝ)+c by positivity) hBound
    (by norm_num : |(0 : ℝ)|≤1/4)).1
  have hFirst : ProphetSecretary.Probability.poissonPayoffFirst (B.completeWorldLaw π.seedLaw) (B.bandRate S)
      (completeBandCount S) (π.scalarPayoff w c) 0=π.scalarBandLikelihoodDerivative S w c := by
    unfold ProphetSecretary.Probability.poissonPayoffFirst RandomizedCountablePolicy.scalarBandLikelihoodDerivative
      bandScore ProphetSecretary.Probability.poissonCenteredScore
    simp only [ProphetSecretary.Probability.poissonLikelihoodFirst_zero]
  rw [hFirst] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : -(1/4 : ℝ)<0) (by norm_num : (0 : ℝ)<1/4)] with θ hθ
  exact π.bandLikelihoodPolicy_scalarMean hS hb hSub (abs_le.mpr hθ) w c

theorem RandomizedCountablePolicy.hasDerivAt_expectedDuration_bandLikelihoodPolicy
    {B : CountableInstance} (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b) :
    HasDerivAt (fun θ => (π.bandLikelihoodPolicy hS hb hSub θ).expectedDuration)
      (∫ v, π.rule.realizedDuration v*B.bandScore S v ∂B.completeWorldLaw π.seedLaw) 0 := by
  have hBound : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, |π.rule.realizedDuration v|≤1 :=
    Eventually.of_forall (fun v => by rw [abs_of_nonneg (π.rule.duration_bounds v).1]; exact (π.rule.duration_bounds v).2)
  have hd := (ProphetSecretary.Probability.poissonPayoff_derivatives (B.completeWorldLaw π.seedLaw) (B.bandRate S)
    (completeBandCount S) (measurable_completeBandCount hS) (B.completeBandCount_hasLaw hS hb hSub π.seedLaw)
    π.rule.realizedDuration (π.rule.measurable_realizedDuration π.measurable_rule) (by norm_num : (0 : ℝ)≤1) hBound
    (by norm_num : |(0 : ℝ)|≤1/4)).1
  have hFirst : ProphetSecretary.Probability.poissonPayoffFirst (B.completeWorldLaw π.seedLaw) (B.bandRate S)
      (completeBandCount S) π.rule.realizedDuration 0=
      ∫ v, π.rule.realizedDuration v*B.bandScore S v ∂B.completeWorldLaw π.seedLaw := by
    unfold ProphetSecretary.Probability.poissonPayoffFirst bandScore ProphetSecretary.Probability.poissonCenteredScore
    simp only [ProphetSecretary.Probability.poissonLikelihoodFirst_zero]
  rw [hFirst] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : -(1/4 : ℝ)<0) (by norm_num : (0 : ℝ)<1/4)] with θ hθ
  exact π.bandLikelihoodPolicy_durationMean hS hb hSub (abs_le.mpr hθ)

end ProphetSecretary.Limiting
