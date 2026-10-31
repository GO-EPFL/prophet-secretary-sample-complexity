import ProphetSecretary.Limiting.CountableCenteredIndividualEnvelope
import ProphetSecretary.Probability.FairSigns

/-!
# Independent fair-sign perturbations of an individual value

One independent fair sign is revealed at the affected occurrence. The actual
displayed law has its scalar derivative zero; equivalently its scalar value
change is o(h). Both signs of h use the same positive-support radius.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal

namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Probability

noncomputable def symmetricIndividualAmplitude (ψ : ℝ → ℝ) (z : ℝ × (Fin 1 → Bool)) : ℝ :=
  variableSign z.2 0*ψ z.1

lemma measurable_symmetricIndividualAmplitude {ψ : ℝ → ℝ} (hψ : Measurable ψ) :
    Measurable (symmetricIndividualAmplitude ψ) :=
  (((measurable_of_countable (fun s : Fin 1 → Bool => variableSign s 0)).comp measurable_snd).mul (hψ.comp measurable_fst))

lemma symmetricIndividualAmplitude_bound {ψ : ℝ → ℝ} {D : ℝ} (hBound : ∀ x, |ψ x|≤D)
    (z : ℝ × (Fin 1 → Bool)) : |symmetricIndividualAmplitude ψ z|≤D := by
  rw [symmetricIndividualAmplitude,abs_mul,abs_variableSign,one_mul]
  exact hBound _

lemma symmetricIndividualAmplitude_vanish {ψ : ℝ → ℝ} {b : ℝ} (hVanish : ∀ x, x<b → ψ x=0)
    (z : ℝ × (Fin 1 → Bool)) (hz : z.1<b) : symmetricIndividualAmplitude ψ z=0 := by
  rw [symmetricIndividualAmplitude,hVanish _ hz,mul_zero]

lemma symmetricIndividualAmplitude_centered (ψ : ℝ → ℝ) (x : ℝ) :
    (∫ s, symmetricIndividualAmplitude ψ (x,s) ∂fairSigns 1)=0 := by
  change (∫ s, variableSign s 0*ψ x ∂fairSigns 1)=0
  rw [integral_mul_const,integral_variableSign,zero_mul]

noncomputable def symmetricIndividualValuePath (B : CountableInstance) (i : ℕ) (ψ : ℝ → ℝ) (hψ : Measurable ψ)
    (D b : ℝ) (hD : 0≤D) (hb : 0<b) (hBound : ∀ x, |ψ x|≤D) (hVanish : ∀ x, x<b → ψ x=0) (θ : ℝ) : CountableInstance :=
  B.individualPayloadValuePath i (fairSigns 1) (symmetricIndividualAmplitude ψ) (measurable_symmetricIndividualAmplitude hψ) D b hD hb
    (symmetricIndividualAmplitude_bound hBound) (symmetricIndividualAmplitude_vanish hVanish) θ

theorem hasDerivAt_optimalScalarValue_symmetricIndividualValuePath (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ) (ψ : ℝ → ℝ) (hψ : Measurable ψ)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ x, |ψ x|≤D) (hVanish : ∀ x, x<b → ψ x=0) :
    HasDerivAt (fun θ => (B.symmetricIndividualValuePath i ψ hψ D b hD hb hBound hVanish θ).optimalScalarValue w c) 0 0 :=
  B.hasDerivAt_optimalScalarValue_centeredIndividualPayload hZero hw hc i (fairSigns 1) (symmetricIndividualAmplitude ψ)
    (measurable_symmetricIndividualAmplitude hψ) hD hb (symmetricIndividualAmplitude_bound hBound)
    (symmetricIndividualAmplitude_vanish hVanish) (symmetricIndividualAmplitude_centered ψ)

theorem symmetricIndividualValuePath_scalar_change_isLittleO (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ) (ψ : ℝ → ℝ) (hψ : Measurable ψ)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ x, |ψ x|≤D) (hVanish : ∀ x, x<b → ψ x=0) :
    (fun θ => (B.symmetricIndividualValuePath i ψ hψ D b hD hb hBound hVanish θ).optimalScalarValue w c-B.optimalScalarValue w c)
      =o[𝓝 (0 : ℝ)] (fun θ => θ) := by
  have hd := B.hasDerivAt_optimalScalarValue_symmetricIndividualValuePath hZero hw hc i ψ hψ hD hb hBound hVanish
  have hAtZero : (B.symmetricIndividualValuePath i ψ hψ D b hD hb hBound hVanish 0).optimalScalarValue w c=B.optimalScalarValue w c := by
    change (B.individualPayloadValuePath i (fairSigns 1) (symmetricIndividualAmplitude ψ) (measurable_symmetricIndividualAmplitude hψ) D b hD hb
      (symmetricIndividualAmplitude_bound hBound) (symmetricIndividualAmplitude_vanish hVanish) 0).optimalScalarValue w c=_
    rw [B.individualPayloadValuePath_zero]
    exact B.withCap_optimalScalarValue _ _ w c
  have h := hasDerivAt_iff_isLittleO.mp hd
  simpa only [hAtZero,sub_zero,smul_zero] using h

end ProphetSecretary.Limiting.CountableInstance
