import ProphetSecretary.Limiting.CountableCenteredPoissonNonnegative
import ProphetSecretary.Limiting.CountableSymmetricIndividualValue

/-!
# Independent symmetric perturbations of all Poisson marks

A fresh independent fair sign accompanies each anonymous occurrence. Its
centered amplitude is revealed only at that occurrence and in the strict
past. The actual scalar change is nonnegative and o(h).
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Probability

noncomputable def symmetricPoissonValuePath (B : CountableInstance) (hZero : B.terminal=0)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (D b : ℝ) (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |ψ x|≤D) (hVanish : ∀ x, x<b → ψ x=0) (θ : ℝ) : CountableInstance :=
  B.poissonPayloadValuePath hZero (fairSigns 1) (symmetricIndividualAmplitude ψ)
    (measurable_symmetricIndividualAmplitude hψ) D b hD hb
    (symmetricIndividualAmplitude_bound hBound) (symmetricIndividualAmplitude_vanish hVanish) θ

theorem hasDerivAt_optimalScalarValue_symmetricPoissonValuePath (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b : ℝ} (hw : 0<w) (hc : 0<c)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |ψ x|≤D) (hVanish : ∀ x, x<b → ψ x=0) :
    HasDerivAt (fun θ => (B.symmetricPoissonValuePath hZero ψ hψ D b hD hb hBound hVanish θ).optimalScalarValue w c) 0 0 :=
  B.hasDerivAt_optimalScalarValue_centeredPoissonPayload hZero hw hc hD hb (fairSigns 1)
    (fun _ : Fin 1 => false) (symmetricIndividualAmplitude ψ) (measurable_symmetricIndividualAmplitude hψ)
    (symmetricIndividualAmplitude_bound hBound) (symmetricIndividualAmplitude_vanish hVanish)
    (symmetricIndividualAmplitude_centered ψ)

theorem symmetricPoissonValuePath_scalar_change_isLittleO (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b : ℝ} (hw : 0<w) (hc : 0<c)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |ψ x|≤D) (hVanish : ∀ x, x<b → ψ x=0) :
    (fun θ => (B.symmetricPoissonValuePath hZero ψ hψ D b hD hb hBound hVanish θ).optimalScalarValue w c-B.optimalScalarValue w c)
      =o[𝓝 (0 : ℝ)] (fun θ => θ) := by
  have hd := B.hasDerivAt_optimalScalarValue_symmetricPoissonValuePath hZero hw hc ψ hψ hD hb hBound hVanish
  have hAtZero : (B.symmetricPoissonValuePath hZero ψ hψ D b hD hb hBound hVanish 0).optimalScalarValue w c=B.optimalScalarValue w c := by
    change (B.poissonPayloadValuePath hZero (fairSigns 1) (symmetricIndividualAmplitude ψ)
      (measurable_symmetricIndividualAmplitude hψ) D b hD hb
      (symmetricIndividualAmplitude_bound hBound) (symmetricIndividualAmplitude_vanish hVanish) 0).optimalScalarValue w c=_
    rw [B.poissonPayloadValuePath_zero]
    exact B.withCap_optimalScalarValue _ _ w c
  have h := hasDerivAt_iff_isLittleO.mp hd
  simpa only [hAtZero,sub_zero,smul_zero] using h

theorem symmetricPoissonValuePath_scalar_change_nonnegative (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b θ : ℝ} (hw : 0<w) (hc : 0<c)
    (ψ : ℝ → ℝ) (hψ : Measurable ψ) (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |ψ x|≤D) (hVanish : ∀ x, x<b → ψ x=0)
    (hθ : |θ|≤ individualValueRadius D b) :
    0≤(B.symmetricPoissonValuePath hZero ψ hψ D b hD hb hBound hVanish θ).optimalScalarValue w c-B.optimalScalarValue w c :=
  sub_nonneg.mpr (B.optimalScalarValue_centeredPoissonPayload_ge_base hZero hw hc hD hb (fairSigns 1)
    (fun _ : Fin 1 => false) (symmetricIndividualAmplitude ψ) (measurable_symmetricIndividualAmplitude hψ)
    (symmetricIndividualAmplitude_bound hBound) (symmetricIndividualAmplitude_vanish hVanish)
    (symmetricIndividualAmplitude_centered ψ) hθ)

end ProphetSecretary.Limiting.CountableInstance
