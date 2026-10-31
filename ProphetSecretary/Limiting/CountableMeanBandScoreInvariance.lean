import ProphetSecretary.Limiting.CountableMeanDurationCoupling
import ProphetSecretary.Limiting.CountableBandScore

/-!
# Poisson duration scores survive an individual mean contraction

The actual canonical duration coupling under mean substitution preserves any
integrable score unchanged by that substitution. Complete Poisson counts and
their intensity centering are unchanged, even when the count includes points
arriving after stopping. Thus the zero-response subcase survives each finite
individual contraction, without differentiating a reoptimized policy.
-/
open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

theorem canonical_band_durationScore_zero_after_mean (B : CountableInstance) (hTerminal : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ)
    (hIndividual : ∀ φ : ℝ → ℝ, Measurable φ → (∀ x, |φ x|≤1) →
      (∫ x, φ x ∂(B.individuals i : Measure ℝ))=0 →
      (∫ v : CompleteWorld Unit, φ (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))=0)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ)<b) (hSub : S ⊆ Ioi b)
    (hBand : (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore S v
      ∂B.completeWorldLaw (Measure.dirac ()))=0) :
    (∫ v : CompleteWorld Unit, ((B.contractIndividual i).valueRule w c).realizedDuration v*
      (B.contractIndividual i).bandScore S v ∂(B.contractIndividual i).completeWorldLaw (Measure.dirac ()))=0 := by
  have hInvariant : ∀ᵐ v : CompleteWorld Unit ∂B.completeWorldLaw (Measure.dirac ()),
      B.bandScore S (replaceIndividualValue i (v,B.individualMean i))=B.bandScore S v :=
    Eventually.of_forall (fun _ => rfl)
  have hTransport := (B.canonical_durationScore_contractIndividual hTerminal hw hc i hIndividual
    (B.bandScore S) (B.measurable_bandScore hS) (B.integrable_bandScore hS hb hSub (Measure.dirac ())) hInvariant).2
  have hScore : (B.contractIndividual i).bandScore (Seed := Unit) S=B.bandScore (Seed := Unit) S := rfl
  rw [hScore]
  calc
    _ = ∫ v : CompleteWorld Unit, B.bandScore S v*((B.contractIndividual i).valueRule w c).realizedDuration v
        ∂(B.contractIndividual i).completeWorldLaw (Measure.dirac ()) :=
      integral_congr_ae (Eventually.of_forall (fun v => mul_comm _ _))
    _ = ∫ v : CompleteWorld Unit, B.bandScore S v*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()) := hTransport
    _ = 0 := by simpa only [mul_comm] using hBand

end ProphetSecretary.Limiting.CountableInstance
