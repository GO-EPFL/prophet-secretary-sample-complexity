import ProphetSecretary.Limiting.CountableNonzeroScores
import ProphetSecretary.Limiting.CountableIndividualResponses
import ProphetSecretary.Limiting.CountableBandResponses

/-!
# Actual fixed-policy duration paths for the nonzero response

Both paths retain the base canonical callback and its independent seed law.
Only the stated individual marginal or marked Poisson intensity changes.
The globally continuous individual score agrees with the centered linear
score on the supported offer interval. Complete Poisson counts are used
only as analytical likelihood scores, including points after stopping.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Probability

noncomputable def linearIndividualDurationPath (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCap : 0<(B.cap : ℝ)) (i : ℕ) (θ : ℝ) : ℝ :=
  ((B.valuePolicy hw hc).individualLikelihoodPolicy i
    (centeredValueScore (B.individuals i : Measure ℝ) B.cap)
    (continuous_centeredValueScore (B.individuals i : Measure ℝ) B.cap).measurable
    (Eventually.of_forall (centeredValueScore_abs_le_one (B.individuals i : Measure ℝ) hCap))
    (centeredValueScore_mean (B.individuals i : Measure ℝ) B.cap) θ).expectedDuration

theorem hasDerivAt_linearIndividualDurationPath (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCap : 0<(B.cap : ℝ)) (i : ℕ) :
    HasDerivAt (B.linearIndividualDurationPath hw hc hCap i)
      (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*
        centeredValueScore (B.individuals i : Measure ℝ) B.cap (v.2.1 i)
          ∂B.completeWorldLaw (Measure.dirac ())) 0 :=
  (B.valuePolicy hw hc).hasDerivAt_expectedDuration_individualLikelihoodPolicy i
    (centeredValueScore (B.individuals i : Measure ℝ) B.cap)
    (continuous_centeredValueScore (B.individuals i : Measure ℝ) B.cap).measurable
    (Eventually.of_forall (centeredValueScore_abs_le_one (B.individuals i : Measure ℝ) hCap))
    (centeredValueScore_mean (B.individuals i : Measure ℝ) B.cap)

noncomputable def positiveBandDurationPath (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ}
    (hb : (B.terminal : ℝ)<b) (hSub : S ⊆ Ioi b) (θ : ℝ) : ℝ :=
  ((B.valuePolicy hw hc).bandLikelihoodPolicy hS hb hSub θ).expectedDuration

theorem hasDerivAt_positiveBandDurationPath (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ}
    (hb : (B.terminal : ℝ)<b) (hSub : S ⊆ Ioi b) :
    HasDerivAt (B.positiveBandDurationPath hw hc hS hb hSub)
      (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
        ∂B.completeWorldLaw (Measure.dirac ())) 0 :=
  (B.valuePolicy hw hc).hasDerivAt_expectedDuration_bandLikelihoodPolicy hS hb hSub

theorem exists_negative_duration_derivative_at_critical (B : CountableInstance) {w c : ℝ}
    (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) :
    (∃ (i : ℕ) (d : ℝ), HasDerivAt (B.linearIndividualDurationPath hw hc (B.cap_pos_of_critical hCritical) i) d 0 ∧ d<0) ∨
    (∃ (S : Set ℝ) (hS : MeasurableSet S) (b : ℝ) (hb : (B.terminal : ℝ)<b) (hSub : S ⊆ Ioi b) (d : ℝ),
      HasDerivAt (B.positiveBandDurationPath hw hc hS hb hSub) d 0 ∧ d<0) := by
  rcases B.exists_negative_duration_score_at_critical hw hc hCritical with hIndividual|hBand
  · obtain ⟨i,hi⟩ := hIndividual
    refine Or.inl ⟨i,_,B.hasDerivAt_linearIndividualDurationPath hw hc (B.cap_pos_of_critical hCritical) i,?_⟩
    simpa only [mul_comm] using hi
  · obtain ⟨S,hS,b,hb,hSub,hNegative⟩ := hBand
    exact Or.inr ⟨S,hS,b,hb,hSub,_,B.hasDerivAt_positiveBandDurationPath hw hc hS hb hSub,hNegative⟩

end ProphetSecretary.Limiting.CountableInstance
