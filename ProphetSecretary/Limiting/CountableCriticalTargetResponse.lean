import ProphetSecretary.Limiting.CountableReverseTargetDerivative
import ProphetSecretary.Limiting.CountableNonzeroDuration

/-!
# A strictly negative actual target response at criticality

The nonzero duration direction is converted to the fixed-base target response
R−T−C(M−1). The parameter is explicitly reversed. The individual score is the
continuous centered linear value score on the supported interval; the Poisson
alternative retains the literal finite upper band and its common continuity
endpoint. This supplies the limiting response used in `prop:critical-input`.
-/

open MeasureTheory Set
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Probability

noncomputable def linearIndividualFixedTargetDifference (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCap : 0<(B.cap : ℝ)) (i : ℕ) (θ : ℝ) : ℝ :=
  B.individualFixedTargetDifference hw hc i
    (centeredValueScore (B.individuals i : Measure ℝ) B.cap)
    (continuous_centeredValueScore (B.individuals i : Measure ℝ) B.cap).measurable
    (Filter.Eventually.of_forall (centeredValueScore_abs_le_one (B.individuals i : Measure ℝ) hCap))
    (centeredValueScore_mean (B.individuals i : Measure ℝ) B.cap) θ

theorem exists_negative_reversed_target_response (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hSum : w+c=1) (hCritical : B.IsCritical w c) :
    (∃ (i : ℕ) (beta : ℝ), 0<beta ∧ HasDerivAt
      (fun θ => B.linearIndividualFixedTargetDifference hw hc (B.cap_pos_of_critical hCritical) i (-θ)) (-beta) 0) ∨
    (∃ (b : ℝ) (_hb : 0<b) (hTerminal : (B.terminal : ℝ)<b),
      B.intensity {b}=0 ∧ (∀ i, (B.individuals i : Measure ℝ) {b}=0) ∧
      0<B.intensity (Ioc b (B.cap : ℝ)) ∧ B.intensity (Ioc b (B.cap : ℝ))<⊤ ∧
      ∃ beta : ℝ, 0<beta ∧ HasDerivAt
        (fun θ => B.bandFixedTargetDifference hw hc (S:=Ioc b (B.cap : ℝ)) measurableSet_Ioc
          hTerminal (fun _ hx => hx.1) (-θ)) (-beta) 0) := by
  rcases B.nonzero_duration_response hw hc hCritical with hI|hBand
  · obtain ⟨i,d,hd,hNeg⟩ := hI
    have hActual := B.hasDerivAt_linearIndividualDurationPath hw hc (B.cap_pos_of_critical hCritical) i
    have hCovNeg : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*
        centeredValueScore (B.individuals i : Measure ℝ) B.cap (v.2.1 i)
          ∂B.completeWorldLaw (Measure.dirac ()))<0 := by
      rw [hActual.unique hd]
      exact hNeg
    have hCoeffNeg : (B.valuePolicy hw hc).scalarIndividualLikelihoodDerivative i 0 1
        (centeredValueScore (B.individuals i : Measure ℝ) B.cap)<0 := by
      simp only [RandomizedCountablePolicy.scalarIndividualLikelihoodDerivative,
        RandomizedCountablePolicy.scalarPayoff,zero_mul,one_mul,zero_add]
      change (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*
        centeredValueScore (B.individuals i : Measure ℝ) B.cap (v.2.1 i)
          ∂B.completeWorldLaw (Measure.dirac ()))<0
      exact hCovNeg
    obtain ⟨beta,hBeta,hDeriv⟩ := B.exists_negative_reversed_individualTargetDerivative hw hc hSum hCritical i
      (centeredValueScore (B.individuals i : Measure ℝ) B.cap)
      (continuous_centeredValueScore (B.individuals i : Measure ℝ) B.cap).measurable
      (Filter.Eventually.of_forall (centeredValueScore_abs_le_one (B.individuals i : Measure ℝ)
        (B.cap_pos_of_critical hCritical)))
      (centeredValueScore_mean (B.individuals i : Measure ℝ) B.cap) hCoeffNeg
    exact Or.inl ⟨i,beta,hBeta,hDeriv⟩
  · obtain ⟨b,hb,hTerminal,hAtom,hAtoms,hPos,hFinite,d,hd,hNeg⟩ := hBand
    have hActual := B.hasDerivAt_positiveBandDurationPath hw hc (S:=Ioc b (B.cap : ℝ))
      measurableSet_Ioc hTerminal (fun _ hx => hx.1)
    have hCovNeg : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*
        B.bandScore (Ioc b (B.cap : ℝ)) v ∂B.completeWorldLaw (Measure.dirac ()))<0 := by
      rw [hActual.unique hd]
      exact hNeg
    have hCoeffNeg : (B.valuePolicy hw hc).scalarBandLikelihoodDerivative (Ioc b (B.cap : ℝ)) 0 1<0 := by
      simp only [RandomizedCountablePolicy.scalarBandLikelihoodDerivative,
        RandomizedCountablePolicy.scalarPayoff,zero_mul,one_mul,zero_add]
      change (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*
        B.bandScore (Ioc b (B.cap : ℝ)) v ∂B.completeWorldLaw (Measure.dirac ()))<0
      exact hCovNeg
    obtain ⟨beta,hBeta,hDeriv⟩ := B.exists_negative_reversed_bandTargetDerivative hw hc hSum hCritical
      (S:=Ioc b (B.cap : ℝ)) measurableSet_Ioc hTerminal (fun _ hx => hx.1) hCoeffNeg
    exact Or.inr ⟨b,hb,hTerminal,hAtom,hAtoms,hPos,hFinite,beta,hBeta,hDeriv⟩

end ProphetSecretary.Limiting.CountableInstance
