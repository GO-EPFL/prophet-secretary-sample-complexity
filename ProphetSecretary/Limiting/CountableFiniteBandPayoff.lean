import ProphetSecretary.Limiting.CountableFiniteBandPolicies
import ProphetSecretary.Probability.PoissonFixedPayoffTaylor

/-!
# Actual fixed-policy scalar expansion under a band intensity tilt

The callbacks, independent auxiliary law and scalar weights are fixed before
changing the offer law. The constant is explicit and independent of instance
size. Reoptimizing the scalar value requires the separate envelope argument.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting
open CountableInstance

namespace CountableInstance

lemma completeWorldLaw_scaleBand_numeric_of_finite (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    (hFinite : B.intensity S<⊤)
    {r : ℝ≥0} (hr : 0 < r) {θ : ℝ} (hParameter : (r : ℝ)=1+θ)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.scaleBand S r).completeWorldLaw ν=(B.completeWorldLaw ν).withDensity
      (fun v => ENNReal.ofReal (ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v))) := by
  rw [B.completeWorldLaw_scaleBand_withDensity_of_finite hS hFinite hr ν]
  apply congrArg (fun f => (B.completeWorldLaw ν).withDensity f)
  funext v
  apply congrArg ENNReal.ofReal
  change Real.exp ((1-(r : ℝ))*B.intensity.real S)*(r : ℝ)^(completeBandCount S v)=
    Real.exp (-(B.bandRate S : ℝ)*θ)*(1+θ)^(completeBandCount S v)
  rw [hParameter,B.bandRate_coe]
  have hExponent : (1-(1+θ))*B.intensity.real S=-(B.intensity.real S)*θ := by ring
  rw [hExponent]

lemma bandLikelihoodPath_completeWorldLaw_numeric_of_finite (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    (hFinite : B.intensity S<⊤) {θ : ℝ} (hθ : |θ| ≤ 1/4)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.bandLikelihoodPath S θ).completeWorldLaw ν=(B.completeWorldLaw ν).withDensity
      (fun v => ENNReal.ofReal (ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v))) := by
  rw [B.bandLikelihoodPath_of_mem S hθ]
  have hPositive : 0 < 1+θ := by linarith only [(abs_le.mp hθ).1]
  exact B.completeWorldLaw_scaleBand_numeric_of_finite hS hFinite hPositive rfl ν

end CountableInstance

lemma RandomizedCountablePolicy.bandLikelihoodPolicy_scalarMean_of_finite {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    (hFinite : B.intensity S<⊤) {θ : ℝ} (hθ : |θ| ≤ 1/4) (w c : ℝ) :
    (π.finiteBandLikelihoodPolicy hS hFinite θ).scalarObjective w c=
      ProphetSecretary.Probability.poissonPayoffMean (B.completeWorldLaw π.seedLaw) (B.bandRate S)
        (completeBandCount S) (π.scalarPayoff w c) θ := by
  have hTerm : (B.bandLikelihoodPath S θ).terminal=B.terminal := by rw [B.bandLikelihoodPath_of_mem S hθ]; rfl
  have hPayoff : (π.finiteBandLikelihoodPolicy hS hFinite θ).scalarPayoff w c=π.scalarPayoff w c := by
    funext v
    exact π.changeInstance_scalarPayoff _ _ hTerm w c v
  rw [(π.finiteBandLikelihoodPolicy hS hFinite θ).scalarObjective_eq_integral,hPayoff]
  change (∫ v : CompleteWorld π.Seed, π.scalarPayoff w c v ∂(B.bandLikelihoodPath S θ).completeWorldLaw π.seedLaw)=_
  rw [B.bandLikelihoodPath_completeWorldLaw_numeric_of_finite hS hFinite hθ π.seedLaw]
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
      π.scalarPayoff w c v=π.scalarPayoff w c v*ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v)
    rw [ENNReal.toReal_ofReal hNonnegative,smul_eq_mul,mul_comm])

theorem RandomizedCountablePolicy.bandLikelihoodPolicy_scalarObjective_taylor_of_finite {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    (hFinite : B.intensity S<⊤) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c)
    {θ : ℝ} (hθ : |θ| ≤ 1/4) :
    |(π.finiteBandLikelihoodPolicy hS hFinite θ).scalarObjective w c-π.scalarObjective w c-
      θ*π.scalarBandLikelihoodDerivative S w c| ≤ 2*(w*(B.cap : ℝ)+c)*θ^2*B.intensity.real S := by
  have hBound : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, |π.scalarPayoff w c v| ≤ w*(B.cap : ℝ)+c :=
    (π.scalarPayoff_bounded hw hc).mono (fun v hv => by rw [abs_of_nonneg hv.1]; exact hv.2)
  have hMeanZero : ProphetSecretary.Probability.poissonPayoffMean (B.completeWorldLaw π.seedLaw) (B.bandRate S)
      (completeBandCount S) (π.scalarPayoff w c) 0=π.scalarObjective w c := by
    simpa only [ProphetSecretary.Probability.poissonPayoffMean,ProphetSecretary.Probability.poissonLikelihood_zero,mul_one] using
      (π.scalarObjective_eq_integral w c).symm
  have hFirstZero : ProphetSecretary.Probability.poissonPayoffFirst (B.completeWorldLaw π.seedLaw) (B.bandRate S)
      (completeBandCount S) (π.scalarPayoff w c) 0=π.scalarBandLikelihoodDerivative S w c := by
    unfold ProphetSecretary.Probability.poissonPayoffFirst RandomizedCountablePolicy.scalarBandLikelihoodDerivative
      bandScore ProphetSecretary.Probability.poissonCenteredScore
    simp only [ProphetSecretary.Probability.poissonLikelihoodFirst_zero]
  have h := ProphetSecretary.Probability.poissonPayoff_taylor_bound (B.completeWorldLaw π.seedLaw) (B.bandRate S)
    (completeBandCount S) (measurable_completeBandCount hS) (B.completeBandCount_hasLaw_of_finite hS hFinite π.seedLaw)
    (π.scalarPayoff w c) (π.measurable_scalarPayoff w c) (show 0 ≤ w*(B.cap : ℝ)+c by positivity) hBound hθ
  rw [← π.bandLikelihoodPolicy_scalarMean_of_finite hS hFinite hθ w c,hMeanZero,hFirstZero] at h
  exact h

end ProphetSecretary.Limiting
