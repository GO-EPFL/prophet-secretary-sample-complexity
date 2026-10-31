import ProphetSecretary.Limiting.CountablePolicyLawTransport
import ProphetSecretary.Limiting.CountableValueRule

/-!
# Enlarging the certified ambient cap

The Poisson construction bands depend on the reserve and intensity, rather
than the cap. Enlarging only the certified upper bound preserves the exact
complete-world law, all callbacks, maxima, scalar values and continuations.
This permits value perturbations whose images extend beyond the old cap.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def withCap (B : CountableInstance) (H : ℝ≥0) (hH : B.cap ≤ H) : CountableInstance where
  cap := H
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap.trans hH
  individuals := B.individuals
  individual_supported i := (B.individual_supported i).mono (fun _ hx => ⟨hx.1,hx.2.trans hH⟩)
  intensity := B.intensity
  intensity_supported := B.intensity_supported.mono (fun _ hx => ⟨hx.1,hx.2.trans hH⟩)
  individual_tail_finite := B.individual_tail_finite
  intensity_tail_finite := B.intensity_tail_finite

lemma withCap_completeWorldLaw (B : CountableInstance) (H : ℝ≥0) (hH : B.cap ≤ H)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) :
    (B.withCap H hH).completeWorldLaw ν=B.completeWorldLaw ν := rfl

lemma withCap_expectedMaximum (B : CountableInstance) (H : ℝ≥0) (hH : B.cap ≤ H) :
    (B.withCap H hH).expectedMaximum=B.expectedMaximum := rfl

lemma withCap_optimalScalarValue (B : CountableInstance) (H : ℝ≥0) (hH : B.cap ≤ H) (w c : ℝ) :
    (B.withCap H hH).optimalScalarValue w c=B.optimalScalarValue w c := by
  rw [B.optimalScalarValue_eq_sSup_transport (B.withCap H hH)
    (fun _ _ hs => hs)
    (fun _ _ hs => hs) w c]
  rfl

lemma withCap_remainingState (B : CountableInstance) (H : ℝ≥0) (hH : B.cap ≤ H)
    (keep : IndividualMask) (u : ℝ≥0) :
    (B.withCap H hH).remainingState keep u=(B.remainingState keep u).withCap H hH := by
  apply CountableInstance.ext_data <;> rfl

lemma withCap_continuationValue (B : CountableInstance) (H : ℝ≥0) (hH : B.cap ≤ H)
    (keep : IndividualMask) (w c : ℝ) (u : ℝ≥0) :
    (B.withCap H hH).continuationValue keep w c u=B.continuationValue keep w c u := by
  change ((B.withCap H hH).remainingState keep u).optimalScalarValue w (c*(u : ℝ))=_
  rw [B.withCap_remainingState H hH]
  exact (B.remainingState keep u).withCap_optimalScalarValue H hH w (c*(u : ℝ))

lemma withCap_valueRule (B : CountableInstance) (H : ℝ≥0) (hH : B.cap ≤ H) (w c : ℝ) :
    (B.withCap H hH).valueRule w c=B.valueRule w c := by
  unfold valueRule
  congr 1
  · funext r t i x history M
    rw [B.withCap_continuationValue H hH]
  · funext r t x history M
    rw [B.withCap_continuationValue H hH]

end ProphetSecretary.Limiting.CountableInstance
