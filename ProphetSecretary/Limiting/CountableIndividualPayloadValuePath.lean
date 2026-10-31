import ProphetSecretary.Limiting.CountableIndividualPayloadDisplacement
import ProphetSecretary.Limiting.CountableIndividualValuePath

/-!
# Two-sided centered payload displacements of one individual

A bounded occurrence amplitude may depend on an independent tag. The explicit
positive-support radius preserves nonnegative offers for both signs, and an
ambient cap larger by one accommodates every displayed value.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting.CountableInstance
variable {T : Type} [MeasurableSpace T]

noncomputable def payloadValueDisplay (A : ℝ × T → ℝ) (D b θ : ℝ) (z : ℝ × T) : ℝ :=
  if |θ|≤ individualValueRadius D b then z.1+θ*A z else z.1

lemma measurable_payloadValueDisplay {A : ℝ × T → ℝ} (hA : Measurable A) (D b θ : ℝ) :
    Measurable (payloadValueDisplay A D b θ) := by
  change Measurable (fun z : ℝ × T => if |θ|≤ individualValueRadius D b then z.1+θ*A z else z.1)
  by_cases hθ : |θ|≤ individualValueRadius D b
  · simp only [if_pos hθ]
    exact measurable_fst.add (hA.const_mul θ)
  · simp only [if_neg hθ]
    exact measurable_fst

omit [MeasurableSpace T] in
lemma payloadValueDisplay_zero (A : ℝ × T → ℝ) (D b : ℝ) : payloadValueDisplay A D b 0=Prod.fst := by
  funext z
  unfold payloadValueDisplay
  split_ifs <;> simp only [zero_mul,add_zero]

lemma payloadValueDisplay_supported (B : CountableInstance) (i : ℕ) (κ : Measure T) [IsProbabilityMeasure κ]
    {A : ℝ × T → ℝ} {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D)
    (hVanish : ∀ z, z.1<b → A z=0) (θ : ℝ) :
    ∀ᵐ z ∂(B.individuals i : Measure ℝ).prod κ, payloadValueDisplay A D b θ z∈Icc (0 : ℝ) (B.cap+1 : ℝ≥0) := by
  have hX : MeasurePreserving (Prod.fst : ℝ × T → ℝ) ((B.individuals i : Measure ℝ).prod κ) (B.individuals i : Measure ℝ) := measurePreserving_fst
  filter_upwards [hX.quasiMeasurePreserving.ae (B.individual_supported i)] with z hz
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
      have hAmpLow := (abs_le.mp (hAmp.trans (min_le_right _ _))).1
      have hAmpHigh := (abs_le.mp (hAmp.trans (min_le_left _ _))).2
      simp only [NNReal.coe_add,NNReal.coe_one]
      exact ⟨by linarith only [not_lt.mp hxb,hAmpLow,hb],by linarith only [hz.2,hAmpHigh]⟩
  · rw [payloadValueDisplay,if_neg hθ]
    exact ⟨hz.1,hz.2.trans (by simp only [NNReal.coe_add,NNReal.coe_one]; linarith)⟩

noncomputable def individualPayloadValuePath (B : CountableInstance) (i : ℕ)
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    (D b : ℝ) (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0) (θ : ℝ) : CountableInstance :=
  (B.withCap (B.cap+1) (by simp)).mapIndividualPayload i κ (payloadValueDisplay A D b θ)
    (measurable_payloadValueDisplay hA D b θ) (B.payloadValueDisplay_supported i κ hD hb hBound hVanish θ)

lemma individualPayloadValuePath_zero (B : CountableInstance) (i : ℕ)
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0) :
    B.individualPayloadValuePath i κ A hA D b hD hb hBound hVanish 0=B.withCap (B.cap+1) (by simp) := by
  apply CountableInstance.ext_data
  · rfl
  · rfl
  · funext j
    change Function.update B.individuals i
      (((B.withCap (B.cap+1) (by simp)).individualPayloadLaw i κ (payloadValueDisplay A D b 0)
        (measurable_payloadValueDisplay hA D b 0))) j=B.individuals j
    by_cases hj : j=i
    · subst j
      rw [Function.update_self]
      apply ProbabilityMeasure.toMeasure_injective
      change ((B.individuals i : Measure ℝ).prod κ).map (payloadValueDisplay A D b 0)=(B.individuals i : Measure ℝ)
      rw [payloadValueDisplay_zero]
      exact (measurePreserving_fst : MeasurePreserving (Prod.fst : ℝ × T → ℝ)
        ((B.individuals i : Measure ℝ).prod κ) (B.individuals i : Measure ℝ)).map_eq
    · rw [Function.update_of_ne hj]
  · rfl

end ProphetSecretary.Limiting.CountableInstance
