import ProphetSecretary.Limiting.CountableCenteredPoissonEnvelope
import ProphetSecretary.Limiting.HybridPoissonPayloadSupport

/-!
# Centered Poisson mark perturbations have nonnegative scalar gain

Each finite base optimizer has zero centered coefficient and is simulated
causally in the displayed model. Passing the two actual value limits proves
the nonnegative change for the full countable policy class.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
variable {T : Type} [MeasurableSpace T] [StandardBorelSpace T]

lemma optimalScalarValue_centeredPoissonPayload_ge_base (B : CountableInstance)
    (hZero : B.terminal=0) {w c D b θ : ℝ} (hw : 0<w) (hc : 0<c) (hD : 0≤D) (hb : 0<b)
    (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T) (A : ℝ × T → ℝ) (hA : Measurable A)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0)
    (hCentered : ∀ x, (∫ t, A (x,t) ∂κ)=0) (hθ : |θ|≤ individualValueRadius D b) :
    B.optimalScalarValue w c≤
      (B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c := by
  obtain ⟨ds,_hAnti,hDs,hDsLim⟩ :=
    (dense_univ : Dense (univ : Set ℝ)).exists_seq_strictAnti_tendsto_of_lt (half_pos hb)
  have hPositive (m : ℕ) : 0<ds m := (hDs m).1.1
  have hSmall (m : ℕ) : ds m<b/2 := (hDs m).1.2
  have hCut (m : ℕ) : (B.terminal : ℝ)<ds m := by simpa only [hZero,NNReal.coe_zero] using hPositive m
  let P := fun m => B.truncation m (ds m) (hCut m)
  have hBase := B.truncation_value_tendsto id ds hCut tendsto_id
    (by simpa only [hZero,NNReal.coe_zero] using hDsLim) hw.le hc.le
  have hNew : Tendsto (fun m => ((P m).poissonPayloadValuePath κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c)
      atTop (𝓝 ((B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c)) := by
    have h := (B.poissonPayloadValuePath hZero κ A hA D b hD hb hBound hVanish θ).truncation_value_tendsto
      id ds hPositive tendsto_id hDsLim hw.le hc.le
    have hEq (m : ℕ) := B.poissonPayloadValuePath_truncation hZero κ A hA hD hb hBound hVanish θ m
      (ds m) (hPositive m) (hSmall m)
    simp only [id_eq] at h
    simpa only [hEq] using h
  apply le_of_tendsto_of_tendsto hBase hNew
  apply Eventually.of_forall
  intro m
  have h := (P m).poissonPayloadValuePath_ge_support hZero hw hc hD hb κ t0 A hA hBound hVanish hθ
  rw [canonicalChronologicalAmplitudeMean_centered _ κ A hA hw.le hc.le hD hBound hCentered,
    mul_zero,mul_zero,add_zero] at h
  exact h

end ProphetSecretary.Limiting.CountableInstance
