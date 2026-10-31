import ProphetSecretary.Limiting.CountableIndividualLikelihoodMaximum
import ProphetSecretary.Limiting.CountableBandStationarity

/-!
# Fixed-policy likelihood coefficients and the critical cross response

Changing coefficients in a payoff keeps the underlying policy fixed. Linearity
of its actual score integrals separates reward and duration responses. At
normalized critical weights, scalar stationarity then gives the target response
R′−T′−CM′=−T′/w.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance

lemma RandomizedCountablePolicy.integral_scalarPayoff_mul_weights {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (score : CompleteWorld π.Seed → ℝ)
    (hR : Integrable (fun v => π.scalarPayoff 1 0 v*score v) (B.completeWorldLaw π.seedLaw))
    (hT : Integrable (fun v => π.scalarPayoff 0 1 v*score v) (B.completeWorldLaw π.seedLaw))
    (w c : ℝ) :
    (∫ v, π.scalarPayoff w c v*score v ∂B.completeWorldLaw π.seedLaw)=
      w*(∫ v, π.scalarPayoff 1 0 v*score v ∂B.completeWorldLaw π.seedLaw)+
      c*(∫ v, π.scalarPayoff 0 1 v*score v ∂B.completeWorldLaw π.seedLaw) := by
  have hEq : (fun v => π.scalarPayoff w c v*score v)=
      (fun v => w*(π.scalarPayoff 1 0 v*score v)+c*(π.scalarPayoff 0 1 v*score v)) := by
    funext v
    unfold RandomizedCountablePolicy.scalarPayoff
    ring
  rw [hEq,integral_add (hR.const_mul w) (hT.const_mul c),integral_const_mul,integral_const_mul]

lemma RandomizedCountablePolicy.scalarIndividualLikelihoodDerivative_weights {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x|≤1) (w c : ℝ) :
    π.scalarIndividualLikelihoodDerivative i w c h=
      w*π.scalarIndividualLikelihoodDerivative i 1 0 h+c*π.scalarIndividualLikelihoodDerivative i 0 1 h := by
  exact π.integral_scalarPayoff_mul_weights (fun v => h (v.2.1 i))
    (π.integrable_scalarIndividualLikelihood i 1 0 hh hb)
    (π.integrable_scalarIndividualLikelihood i 0 1 hh hb) w c

lemma RandomizedCountablePolicy.scalarBandLikelihoodDerivative_weights {B : CountableInstance}
    (π : RandomizedCountablePolicy B) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b) (w c : ℝ) :
    π.scalarBandLikelihoodDerivative S w c=
      w*π.scalarBandLikelihoodDerivative S 1 0+c*π.scalarBandLikelihoodDerivative S 0 1 := by
  exact π.integral_scalarPayoff_mul_weights (B.bandScore S)
    (π.integrable_scalarBandLikelihood hS hb hSub (w:=1) (c:=0) (by norm_num) (by norm_num))
    (π.integrable_scalarBandLikelihood hS hb hSub (w:=0) (c:=1) (by norm_num) (by norm_num)) w c

lemma normalized_stationarity_cross {w c C dR dT dM : ℝ} (hw : w≠0) (hSum : w+c=1)
    (hStat : w*dR+c*dT=C*w*dM) : dR-dT-C*dM= -dT/w := by
  have hSumT : w*dT+c*dT=dT := by rw [←add_mul,hSum,one_mul]
  apply (eq_div_iff hw).mpr
  nlinarith only [hStat,hSumT]

end ProphetSecretary.Limiting
