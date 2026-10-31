import ProphetSecretary.Limiting.CountableSymmetricIndividualValue

/-!
# Nonnegative scalar gain under centered individual perturbations

The base optimizer ignores the independent centered tag. Its causal
conditionally reconstructed displayed-law policy attains exactly the base
scalar value. Optimization therefore makes the scalar change nonnegative.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting.CountableInstance

lemma optimalScalarValue_centeredIndividualPayload_ge_base
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (i : ℕ) {T : Type} [MeasurableSpace T] [StandardBorelSpace T]
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D)
    (hVanish : ∀ z, z.1<b → A z=0) (hCentered : ∀ x, (∫ t, A (x,t) ∂κ)=0)
    {θ : ℝ} (hθ : |θ|≤ individualValueRadius D b) :
    B.optimalScalarValue w c≤(B.individualPayloadValuePath i κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c := by
  let C := B.withCap (B.cap+1) (by simp)
  let π := RandomizedIndividualTaggedPolicy.ignoreTag (C.valuePolicy hw hc) i κ
  have hMean : π.payloadPerturbationMean A=0 := by
    change (∫ v : CompleteWorld (Unit × T), (C.valueRule w c).individualSelectionIndicator i (eraseCompleteSeed v)*A (v.2.1 i,v.2.2.2.2)
      ∂C.completeWorldLaw ((Measure.dirac ()).prod κ))=0
    exact C.canonical_payloadPerturbation_mean_zero hw.le hc.le i (Measure.dirac ()) κ A hA hD hBound hCentered
  have hGain : π.payloadDisplacementMean (payloadValueDisplay A D b θ)=0 := by
    rw [π.payloadDisplacementMean_display A hθ,hMean,mul_zero]
  obtain ⟨policy,hJ⟩ := π.exists_displayedPayloadPolicy_scalarObjective (payloadValueDisplay A D b θ)
    (measurable_payloadValueDisplay hA D b θ) (B.payloadValueDisplay_supported i κ hD hb hBound hVanish θ) w c
  rw [hGain,mul_zero,add_zero] at hJ
  have hBase : π.toBasePolicy.scalarObjective w c=B.optimalScalarValue w c :=
    (RandomizedIndividualTaggedPolicy.ignoreTag_scalarObjective (C.valuePolicy hw hc) i κ w c).trans
      ((C.valuePolicy_optimal hZero hw hc).trans (B.withCap_optimalScalarValue _ _ w c))
  rw [hBase] at hJ
  exact hJ.symm.trans_le ((B.individualPayloadValuePath i κ A hA D b hD hb hBound hVanish θ).scalarObjective_le_value policy w c)

theorem symmetricIndividualValuePath_scalar_change_nonnegative
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (i : ℕ) (ψ : ℝ → ℝ) (hψ : Measurable ψ) {D b : ℝ} (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |ψ x|≤D) (hVanish : ∀ x, x<b → ψ x=0)
    {θ : ℝ} (hθ : |θ|≤ individualValueRadius D b) :
    0≤(B.symmetricIndividualValuePath i ψ hψ D b hD hb hBound hVanish θ).optimalScalarValue w c-B.optimalScalarValue w c :=
  sub_nonneg.mpr (B.optimalScalarValue_centeredIndividualPayload_ge_base hZero hw hc i (ProphetSecretary.Probability.fairSigns 1)
    (symmetricIndividualAmplitude ψ) (measurable_symmetricIndividualAmplitude hψ) hD hb
    (symmetricIndividualAmplitude_bound hBound) (symmetricIndividualAmplitude_vanish hVanish)
    (symmetricIndividualAmplitude_centered ψ) hθ)

end ProphetSecretary.Limiting.CountableInstance
