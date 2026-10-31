import ProphetSecretary.Limiting.CountableNonzeroDurationPaths
import ProphetSecretary.Limiting.CountableUpperBandResponse

/-!
# A nonzero fixed-canonical duration derivative

This is `lem:nonzero` for the constructed countable limiting model. Positive
critical weights supply zero reserve by `lem:no-reserve`. The individual
alternative uses a globally bounded continuous centered value score. The
Poisson alternative uses the literal upper band `(b,H]` at a positive common
continuity level, has positive finite intensity, and differentiates the
duration of the fixed base canonical policy. Policies are transported along
the actual likelihood laws; their callbacks and independent seeds are fixed.
-/
open MeasureTheory Set Filter
open scoped Classical ENNReal
namespace ProphetSecretary.Limiting.CountableInstance

lemma intensity_pos_of_negative_durationScore (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ}
    (hb : (B.terminal : ℝ)<b) (hSub : S ⊆ Ioi b)
    (hNegative : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
      ∂B.completeWorldLaw (Measure.dirac ()))<0) : 0<B.intensity S := by
  apply pos_iff_ne_zero.mpr
  intro hZero
  have hBound := (B.valuePolicy hw hc).scalarBandLikelihoodDerivative_bound hS hb hSub
    (w := 0) (c := 1) (by norm_num) (by norm_num)
  simp only [RandomizedCountablePolicy.scalarBandLikelihoodDerivative,RandomizedCountablePolicy.scalarPayoff,
    zero_mul,one_mul,zero_add,mul_one] at hBound
  change |∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
      ∂B.completeWorldLaw (Measure.dirac ())|≤2*B.intensity.real S at hBound
  rw [measureReal_def,hZero,ENNReal.toReal_zero,mul_zero] at hBound
  exact (ne_of_lt hNegative) (abs_nonpos_iff.mp hBound)

theorem nonzero_duration_response (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) :
    (∃ (i : ℕ) (d : ℝ),
      HasDerivAt (B.linearIndividualDurationPath hw hc (B.cap_pos_of_critical hCritical) i) d 0 ∧ d<0) ∨
    (∃ (b : ℝ) (_hb : 0<b) (hTerminal : (B.terminal : ℝ)<b),
      B.intensity {b}=0 ∧ (∀ i, (B.individuals i : Measure ℝ) {b}=0) ∧
        0<B.intensity (Ioc b (B.cap : ℝ)) ∧ B.intensity (Ioc b (B.cap : ℝ))<⊤ ∧
        ∃ d : ℝ, HasDerivAt
          (B.positiveBandDurationPath hw hc (S := Ioc b (B.cap : ℝ)) measurableSet_Ioc
            hTerminal (fun _ hx => hx.1)) d 0 ∧ d<0) := by
  rcases B.exists_negative_duration_score_at_critical hw hc hCritical with hIndividual|hBand
  · obtain ⟨i,hi⟩ := hIndividual
    refine Or.inl ⟨i,_,B.hasDerivAt_linearIndividualDurationPath hw hc (B.cap_pos_of_critical hCritical) i,?_⟩
    simpa only [mul_comm] using hi
  · obtain ⟨S,hS,b,hb,hSub,hNegative⟩ := hBand
    obtain ⟨a,ha,hTerminal,hAtom,hAtoms,_hUnbounded,hUpper⟩ :=
      B.exists_upperContinuityBand_durationScore_negative hw hc hS hb hSub (ne_of_lt hNegative)
    have hUpperSub : Ioc a (B.cap : ℝ) ⊆ Ioi a := fun _ hx => hx.1
    refine Or.inr ⟨a,ha,hTerminal,hAtom,hAtoms,
      B.intensity_pos_of_negative_durationScore hw hc measurableSet_Ioc hTerminal hUpperSub hUpper,
      B.intensity_band_finite hTerminal hUpperSub,_,?_,hUpper⟩
    exact B.hasDerivAt_positiveBandDurationPath hw hc measurableSet_Ioc hTerminal hUpperSub

end ProphetSecretary.Limiting.CountableInstance
