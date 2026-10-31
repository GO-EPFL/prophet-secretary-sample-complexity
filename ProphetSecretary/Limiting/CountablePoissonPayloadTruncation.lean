import ProphetSecretary.Limiting.CountablePoissonPayloadValuePath

/-!
# Exact truncation of tagged Poisson value perturbations

A cutoff below half the positive support level is preserved by the display.
Consequently the finite hybrid truncation is exactly the finite displayed
payload model, including its retained identities and terminal reward.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting
open CountableInstance
variable {T : Type} [MeasurableSpace T]

omit [MeasurableSpace T] in
lemma payloadValueDisplay_mem_Ioi_iff {A : ℝ × T → ℝ} {D b d θ : ℝ}
    (hD : 0≤D) (hb : 0<b) (hd : d<b/2) (hBound : ∀ z, |A z|≤D)
    (hVanish : ∀ z, z.1<b → A z=0) (z : ℝ × T) :
    d<payloadValueDisplay A D b θ z ↔ d<z.1 := by
  by_cases hxb : z.1<b
  · have hg : payloadValueDisplay A D b θ z=z.1 := by
      unfold payloadValueDisplay
      split_ifs <;> simp only [hVanish z hxb,mul_zero,add_zero]
    rw [hg]
  · have hx : b≤z.1 := not_lt.mp hxb
    have hdX : d<z.1 := by linarith
    have hdG : d<payloadValueDisplay A D b θ z := by
      by_cases hθ : |θ|≤ individualValueRadius D b
      · rw [payloadValueDisplay,if_pos hθ]
        have hAmp : |θ*A z|≤b/2 := by
          calc
            _ = |θ| * |A z| := abs_mul _ _
            _ ≤ |θ| * D := mul_le_mul_of_nonneg_left (hBound z) (abs_nonneg _)
            _ ≤ |θ| * (D+1) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
            _ ≤ min 1 (b/2) := (le_div_iff₀ (by positivity : 0<D+1)).mp hθ
            _ ≤ b/2 := min_le_right _ _
        linarith [(abs_le.mp hAmp).1]
      · rw [payloadValueDisplay,if_neg hθ]
        exact hdX
    exact iff_of_true hdG hdX

lemma CountableInstance.poissonPayloadValuePath_intensityAbove (B : CountableInstance)
    (hZero : B.terminal=0) (κ : Measure T) [IsProbabilityMeasure κ]
    (A : ℝ × T → ℝ) (hA : Measurable A) {D b : ℝ} (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0) (θ d : ℝ)
    (hd : 0<d) (hdb : d<b/2) :
    (B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish θ).intensityAbove d hd=
      displayedPayloadIntensity (B.intensityAbove d (by simpa only [hZero,NNReal.coe_zero] using hd)) κ
        (payloadValueDisplay A D b θ) (measurable_payloadValueDisplay hA D b θ) := by
  apply FiniteMeasure.toMeasure_injective
  change ((B.intensity.prod κ).map (payloadValueDisplay A D b θ)).restrict (Ioi d)=_
  rw [displayedPayloadIntensity_toMeasure,Measure.restrict_map
    (measurable_payloadValueDisplay hA D b θ) measurableSet_Ioi]
  have hPre : payloadValueDisplay A D b θ ⁻¹' Ioi d=Ioi d ×ˢ (univ : Set T) := by
    ext z
    simp only [mem_preimage,mem_Ioi,mem_prod,mem_univ,and_true]
    exact payloadValueDisplay_mem_Ioi_iff hD hb hdb hBound hVanish z
  rw [hPre,← Measure.restrict_prod_eq_prod_univ]
  rfl

private lemma finiteHybrid_eq_of_data {n : ℕ} (P Q : FiniteIntensityHybridInstance n)
    (hCap : P.cap=Q.cap) (hTerm : P.terminal=Q.terminal)
    (hP : P.individuals=Q.individuals) (hμ : P.intensity=Q.intensity) : P=Q := by
  cases P
  cases Q
  cases hCap
  cases hTerm
  cases hP
  cases hμ
  rfl

lemma CountableInstance.poissonPayloadValuePath_truncation (B : CountableInstance)
    (hZero : B.terminal=0) (κ : Measure T) [IsProbabilityMeasure κ]
    (A : ℝ × T → ℝ) (hA : Measurable A) {D b : ℝ} (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0) (θ : ℝ)
    (N : ℕ) (d : ℝ) (hd : 0<d) (hdb : d<b/2) :
    (B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish θ).truncation N d hd=
      (B.truncation N d (by simpa only [hZero,NNReal.coe_zero] using hd)).poissonPayloadValuePath
        κ A hA D b hD hb hBound hVanish θ := by
  apply finiteHybrid_eq_of_data
  · rfl
  · exact hZero.symm
  · rfl
  · exact B.poissonPayloadValuePath_intensityAbove hZero κ A hA hD hb hBound hVanish θ d hd hdb

end ProphetSecretary.Limiting
