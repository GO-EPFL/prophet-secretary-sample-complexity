import ProphetSecretary.Limiting.CountableBandResponses

/-!
# The actual prophet response to a finite positive-band intensity tilt

The raw maximum is a fixed bounded measurable payoff on the full world. Its
likelihood response uses the complete centered band count, including points
arriving after any policy stops.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def prophetBandLikelihoodDerivative (B : CountableInstance) (S : Set ℝ) : ℝ :=
  ∫ v : CompleteWorld Unit, B.maximum (v.1,v.2.1)*B.bandScore S v ∂B.completeWorldLaw (Measure.dirac ())

lemma expectedMaximum_bandLikelihoodPath_mean (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b) {θ : ℝ} (hθ : |θ|≤1/4) :
    (B.bandLikelihoodPath S θ).expectedMaximum=
      ProphetSecretary.Probability.poissonPayoffMean (B.completeWorldLaw (Measure.dirac ())) (B.bandRate S)
        (completeBandCount S) (fun v : CompleteWorld Unit => B.maximum (v.1,v.2.1)) θ := by
  let Q := B.bandLikelihoodPath S θ
  have hProjection := (Q.value_projection_measurePreserving (Measure.dirac ())).hasLaw.integral_comp Q.measurable_maximum.aestronglyMeasurable
  have hTerm : Q.terminal=B.terminal := by
    change (B.bandLikelihoodPath S θ).terminal=B.terminal
    rw [bandLikelihoodPath_of_mem B S hθ]
    rfl
  have hMaximum : Q.maximum=B.maximum := by funext v; change countableMaximum Q.terminal _=countableMaximum B.terminal _; rw [hTerm]
  change (∫ v, Q.maximum v ∂Q.valueLaw)=_
  rw [← hProjection,hMaximum]
  change (∫ v : CompleteWorld Unit, B.maximum (v.1,v.2.1) ∂(B.bandLikelihoodPath S θ).completeWorldLaw (Measure.dirac ()))=_
  rw [B.bandLikelihoodPath_completeWorldLaw_numeric hS hb hSub hθ (Measure.dirac ())]
  have hDensity : Measurable (fun v : CompleteWorld Unit => ENNReal.ofReal
      (ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v))) :=
    ENNReal.measurable_ofReal.comp ((measurable_of_countable
      (ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ)).comp (measurable_completeBandCount hS))
  rw [integral_withDensity_eq_integral_toReal_smul hDensity (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by
    have hPositive : 0<1+θ := by linarith only [(abs_le.mp hθ).1]
    have hNonnegative : 0≤ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v) :=
      mul_nonneg (Real.exp_pos _).le (pow_nonneg hPositive.le _)
    change (ENNReal.ofReal (ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v))).toReal •
      B.maximum (v.1,v.2.1)=B.maximum (v.1,v.2.1)*ProphetSecretary.Probability.poissonLikelihood (B.bandRate S) θ (completeBandCount S v)
    rw [ENNReal.toReal_ofReal hNonnegative,smul_eq_mul,mul_comm])

theorem hasDerivAt_expectedMaximum_bandLikelihoodPath (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S⊆Ioi b) :
    HasDerivAt (fun θ => (B.bandLikelihoodPath S θ).expectedMaximum) (B.prophetBandLikelihoodDerivative S) 0 := by
  have hProjection := B.value_projection_measurePreserving (Measure.dirac ())
  have hMeas : Measurable (fun v : CompleteWorld Unit => B.maximum (v.1,v.2.1)) := B.measurable_maximum.comp hProjection.measurable
  have hBound : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()), |B.maximum (v.1,v.2.1)|≤B.cap :=
    (hProjection.quasiMeasurePreserving.ae B.maximum_bounded).mono (fun v hv => by
      rw [abs_of_nonneg (B.terminal.property.trans hv.1)]
      exact hv.2)
  have hd := (ProphetSecretary.Probability.poissonPayoff_derivatives (B.completeWorldLaw (Measure.dirac ())) (B.bandRate S)
    (completeBandCount S) (measurable_completeBandCount hS) (B.completeBandCount_hasLaw hS hb hSub (Measure.dirac ()))
    (fun v : CompleteWorld Unit => B.maximum (v.1,v.2.1)) hMeas B.cap.property hBound (by norm_num : |(0 : ℝ)|≤1/4)).1
  have hCoeff : ProphetSecretary.Probability.poissonPayoffFirst (B.completeWorldLaw (Measure.dirac ())) (B.bandRate S)
      (completeBandCount S) (fun v : CompleteWorld Unit => B.maximum (v.1,v.2.1)) 0=B.prophetBandLikelihoodDerivative S := by
    unfold ProphetSecretary.Probability.poissonPayoffFirst prophetBandLikelihoodDerivative bandScore ProphetSecretary.Probability.poissonCenteredScore
    simp only [ProphetSecretary.Probability.poissonLikelihoodFirst_zero]
  rw [hCoeff] at hd
  apply hd.congr_of_eventuallyEq
  filter_upwards [Icc_mem_nhds (by norm_num : -(1/4 : ℝ)<0) (by norm_num : (0 : ℝ)<1/4)] with θ hθ
  exact B.expectedMaximum_bandLikelihoodPath_mean hS hb hSub (abs_le.mpr hθ)

end ProphetSecretary.Limiting.CountableInstance
