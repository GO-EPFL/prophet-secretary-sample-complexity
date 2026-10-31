import ProphetSecretary.Limiting.HybridPoissonPayloadInstance
import ProphetSecretary.Limiting.PoissonPayloadDisplay
import ProphetSecretary.Limiting.CountableIndividualPayloadValuePath

/-!
# Actual finite-hybrid Poisson value-perturbation families

The existing bounded-amplitude display is used for both signs. Positive
support preserves strict positivity of actual Poisson marks, and the cap is
increased by one. The explicit radius and displacement bound are independent
of retained dimension and total Poisson mass.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting
open CountableInstance
variable {T : Type} [MeasurableSpace T]

omit [MeasurableSpace T] in
lemma payloadValueDisplay_positive_bounds {A : ℝ × T → ℝ} {D b : ℝ} {H : ℝ≥0}
    (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0)
    (θ : ℝ) (z : ℝ × T) (hz : z.1∈Ioc (0 : ℝ) H) :
    payloadValueDisplay A D b θ z∈Ioc (0 : ℝ) (H+1 : ℝ≥0) := by
  by_cases hθ : |θ|≤ individualValueRadius D b
  · rw [payloadValueDisplay,if_pos hθ]
    by_cases hxb : z.1<b
    · rw [hVanish z hxb,mul_zero,add_zero]
      exact ⟨hz.1,hz.2.trans (by simp only [NNReal.coe_add,NNReal.coe_one]; linarith)⟩
    · have hAmp : |θ*A z|≤min 1 (b/2) := by
        calc
          _ = |θ| * |A z| := abs_mul _ _
          _ ≤ |θ| * D := mul_le_mul_of_nonneg_left (hBound z) (abs_nonneg _)
          _ ≤ |θ| * (D+1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
          _ ≤ min 1 (b/2) := (le_div_iff₀ (by positivity : 0<D+1)).mp hθ
      have hLow := (abs_le.mp (hAmp.trans (min_le_right _ _))).1
      have hHigh := (abs_le.mp (hAmp.trans (min_le_left _ _))).2
      simp only [NNReal.coe_add,NNReal.coe_one]
      exact ⟨by linarith only [not_lt.mp hxb,hLow,hb],by linarith only [hz.2,hHigh]⟩
  · rw [payloadValueDisplay,if_neg hθ]
    exact ⟨hz.1,hz.2.trans (by simp only [NNReal.coe_add,NNReal.coe_one]; linarith)⟩

omit [MeasurableSpace T] in
lemma payloadValueDisplay_displacement_bound {A : ℝ × T → ℝ} {D b : ℝ}
    (hD : 0≤D) (hBound : ∀ z, |A z|≤D) (θ : ℝ) (z : ℝ × T) :
    |payloadValueDisplay A D b θ z-z.1|≤|θ| * D := by
  by_cases hθ : |θ|≤ individualValueRadius D b
  · rw [payloadValueDisplay,if_pos hθ,add_sub_cancel_left,abs_mul]
    exact mul_le_mul_of_nonneg_left (hBound z) (abs_nonneg _)
  · rw [payloadValueDisplay,if_neg hθ,sub_self,abs_zero]
    exact mul_nonneg (abs_nonneg _) hD

lemma FiniteIntensityHybridInstance.payloadValueDisplay_supported {n : ℕ}
    (B : FiniteIntensityHybridInstance n) (κ : Measure T) [IsProbabilityMeasure κ]
    {A : ℝ × T → ℝ} {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D)
    (hVanish : ∀ z, z.1<b → A z=0) (θ : ℝ) :
    ∀ᵐ z ∂(B.intensity : Measure ℝ).prod κ, payloadValueDisplay A D b θ z∈Ioc (0 : ℝ) (B.cap+1 : ℝ≥0) := by
  have hMP : MeasurePreserving (Prod.fst : ℝ × T → ℝ) ((B.intensity : Measure ℝ).prod κ) (B.intensity : Measure ℝ) := measurePreserving_fst
  exact (hMP.quasiMeasurePreserving.ae B.intensity_supported).mono (fun z hz =>
    payloadValueDisplay_positive_bounds hD hb hBound hVanish θ z hz)

noncomputable def FiniteIntensityHybridInstance.poissonPayloadValuePath {n : ℕ}
    (B : FiniteIntensityHybridInstance n) (κ : Measure T) [IsProbabilityMeasure κ]
    (A : ℝ × T → ℝ) (hA : Measurable A) (D b : ℝ) (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0) (θ : ℝ) : FiniteIntensityHybridInstance n :=
  B.displayPoissonPayload (B.cap+1) (by simp) κ (payloadValueDisplay A D b θ)
    (measurable_payloadValueDisplay hA D b θ) (B.payloadValueDisplay_supported κ hD hb hBound hVanish θ)

lemma FiniteIntensityHybridInstance.poissonPayloadValuePath_scalar_zero {n : ℕ}
    (B : FiniteIntensityHybridInstance n) (κ : Measure T) [IsProbabilityMeasure κ]
    (A : ℝ × T → ℝ) (hA : Measurable A) {D b : ℝ} (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0) (π : RandomizedHybridPolicy n) (w c : ℝ) :
    π.scalarObjective (B.poissonPayloadValuePath κ A hA D b hD hb hBound hVanish 0) w c=π.scalarObjective B w c := by
  have hIntensity : displayedPayloadIntensity B.intensity κ (payloadValueDisplay A D b 0) (measurable_payloadValueDisplay hA D b 0)=B.intensity := by
    apply FiniteMeasure.toMeasure_injective
    rw [displayedPayloadIntensity_toMeasure]
    rw [payloadValueDisplay_zero]
    exact (measurePreserving_fst : MeasurePreserving (Prod.fst : ℝ × T → ℝ)
      ((B.intensity : Measure ℝ).prod κ) (B.intensity : Measure ℝ)).map_eq
  change (∫ v, w*π.rule.realizedReward B.terminal v+c*π.rule.realizedDuration v
    ∂hybridWorldLaw B.individuals (displayedPayloadIntensity B.intensity κ (payloadValueDisplay A D b 0)
      (measurable_payloadValueDisplay hA D b 0)) π.seedLaw)=_
  rw [hIntensity]
  rfl

lemma FiniteIntensityHybridInstance.poissonPayloadValuePath_value_zero {n : ℕ}
    (B : FiniteIntensityHybridInstance n) (κ : Measure T) [IsProbabilityMeasure κ]
    (A : ℝ × T → ℝ) (hA : Measurable A) {D b : ℝ} (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0) (w c : ℝ) :
    (B.poissonPayloadValuePath κ A hA D b hD hb hBound hVanish 0).optimalScalarValue w c=B.optimalScalarValue w c := by
  unfold FiniteIntensityHybridInstance.optimalScalarValue FiniteIntensityHybridInstance.scalarPayoffs
  apply congrArg sSup
  apply congrArg Set.range
  funext π
  exact B.poissonPayloadValuePath_scalar_zero κ A hA hD hb hBound hVanish π w c

end ProphetSecretary.Limiting
