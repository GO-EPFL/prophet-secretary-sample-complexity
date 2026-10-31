import ProphetSecretary.Limiting.CountableIndividualEnvelope
import ProphetSecretary.Limiting.CountableIndividualResponses
import ProphetSecretary.Limiting.NoReserve
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-!
# The actual prophet response to an individual likelihood tilt

The maximum is a fixed bounded payoff on the full world, including offers
after stopping. Its affine likelihood expectation is established before the
optimized scalar envelope is used to obtain critical stationarity.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model

noncomputable def prophetIndividualLikelihoodDerivative (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ) : ℝ :=
  ∫ v : CompleteWorld Unit, B.maximum (v.1,v.2.1)*h (v.2.1 i) ∂B.completeWorldLaw (Measure.dirac ())

lemma expectedMaximum_individualLikelihoodPath_affine (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x|≤1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) {θ : ℝ} (hθ : |θ|≤1/4) :
    (B.individualLikelihoodPath i h hh hb hm θ).expectedMaximum=
      B.expectedMaximum+θ*B.prophetIndividualLikelihoodDerivative i h := by
  let Q := B.individualLikelihoodPath i h hh hb hm θ
  let F := fun v : CompleteWorld Unit => B.maximum (v.1,v.2.1)
  have hProjection := (Q.value_projection_measurePreserving (Measure.dirac ())).hasLaw.integral_comp Q.measurable_maximum.aestronglyMeasurable
  have hTerm : Q.terminal=B.terminal := by
    change (B.individualLikelihoodPath i h hh hb hm θ).terminal=B.terminal
    rw [B.individualLikelihoodPath_of_mem i h hh hb hm hθ]
    rfl
  have hMaximum : Q.maximum=B.maximum := by
    funext v
    change countableMaximum Q.terminal _=countableMaximum B.terminal _
    rw [hTerm]
  have hMP := B.value_projection_measurePreserving (Measure.dirac ())
  have hFI : Integrable F (B.completeWorldLaw (Measure.dirac ())) :=
    hMP.integrable_comp_of_integrable B.integrable_maximum
  have hBase : (∫ v, F v ∂B.completeWorldLaw (Measure.dirac ()))=B.expectedMaximum :=
    hMP.hasLaw.integral_comp B.measurable_maximum.aestronglyMeasurable
  change (∫ v, Q.maximum v ∂Q.valueLaw)=_
  rw [←hProjection,hMaximum]
  change (∫ v, F v ∂(B.individualLikelihoodPath i h hh hb hm θ).completeWorldLaw (Measure.dirac ()))=_
  rw [B.individualLikelihoodPath_of_mem i h hh hb hm hθ,
    B.individualLikelihoodTilt_completeWorldLaw i h hh hb hm θ hθ (Measure.dirac ()),
    ProphetSecretary.Probability.integral_tiltLaw_eq_add (measurable_individualScore i hh)
      (B.individualScore_bounded_ae (Measure.dirac ()) i hb) hFI hθ,hBase]
  rfl

theorem hasDerivAt_expectedMaximum_individualLikelihoodPath (B : CountableInstance) (i : ℕ) (h : ℝ → ℝ)
    (hh : Measurable h) (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x|≤1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) :
    HasDerivAt (fun θ => (B.individualLikelihoodPath i h hh hb hm θ).expectedMaximum)
      (B.prophetIndividualLikelihoodDerivative i h) 0 := by
  have hAffine : HasDerivAt (fun θ : ℝ => B.expectedMaximum+θ*B.prophetIndividualLikelihoodDerivative i h)
      (B.prophetIndividualLikelihoodDerivative i h) 0 := (hasDerivAt_mul_const (x:=0) _).const_add _
  apply hAffine.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : -(1/4 : ℝ)<0) (by norm_num : (0 : ℝ)<1/4)] with θ hθ
  exact B.expectedMaximum_individualLikelihoodPath_affine i h hh hb hm (abs_le.mpr hθ)

theorem critical_individual_likelihood_stationarity (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    (i : ℕ) (h : ℝ → ℝ) (hh : Measurable h)
    (hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x|≤1)
    (hm : ∫ x, h x ∂(B.individuals i : Measure ℝ)=0) :
    (B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i w c h=
      optimalCompetitiveRatio*w*B.prophetIndividualLikelihoodDerivative i h := by
  have hZero := B.terminal_eq_zero_of_critical hw hc.le hCritical
  have hBaseGap : (B.individualLikelihoodPath i h hh hb hm 0).scalarGap w c=0 := by
    rw [B.individualLikelihoodPath_zero]
    exact hCritical.2
  have hMin : IsLocalMin (fun θ => (B.individualLikelihoodPath i h hh hb hm θ).scalarGap w c) 0 := by
    change ∀ᶠ θ in 𝓝 (0 : ℝ), (B.individualLikelihoodPath i h hh hb hm 0).scalarGap w c≤
      (B.individualLikelihoodPath i h hh hb hm θ).scalarGap w c
    rw [hBaseGap]
    exact Filter.Eventually.of_forall (fun θ => (B.individualLikelihoodPath i h hh hb hm θ).scalarGap_nonnegative hw.le hc.le)
  have hV := B.hasDerivAt_optimalScalarValue_individualLikelihoodPath hZero hw hc i h hh hb hm
  have hM := B.hasDerivAt_expectedMaximum_individualLikelihoodPath i h hh hb hm
  have hGap := hV.sub (((hM.const_mul w).add_const c).const_mul optimalCompetitiveRatio)
  have hStat := hMin.hasDerivAt_eq_zero hGap
  nlinarith only [hStat]

end ProphetSecretary.Limiting.CountableInstance
