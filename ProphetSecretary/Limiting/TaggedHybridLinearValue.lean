import ProphetSecretary.Limiting.TaggedHybridCommonPolicies
import ProphetSecretary.Limiting.HybridPoissonValuePath

/-!
# A common affine payoff representation of Poisson value perturbations

The same causal tagged-policy class is used for both signs of the parameter.
Only a fixed policy's selected anonymous amplitude is differentiated.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance

noncomputable def RandomizedTaggedHybridPolicy.payloadAmplitudeMean {n : ℕ} {T : Type}
    [MeasurableSpace T] (π : RandomizedTaggedHybridPolicy n T) (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) (t0 : T) (A : ℝ × T → ℝ) : ℝ :=
  ∫ v, π.rule.payloadSelectedAmplitude t0 A v ∂taggedHybridWorldLaw B π.seedLaw κ

lemma TaggedHybridRule.payloadSelectedAmplitude_const_mul {n : ℕ} {Seed T : Type*}
    [MeasurableSpace T] (π : TaggedHybridRule n Seed T) (t0 : T) (A : ℝ × T → ℝ)
    (θ : ℝ) (v : PayloadConfiguration T × Model.World n Seed) :
    π.payloadSelectedAmplitude t0 (fun z => θ*A z) v=θ*π.payloadSelectedAmplitude t0 A v := by
  unfold TaggedHybridRule.payloadSelectedAmplitude Model.Policy.selectedTag
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  by_cases hk : (π.sampleTags.asFinitePolicy v.1.1).ActualSelects
      (v.2.2.2,payloadTagSequence t0 v.1) Finset.univ
      (combinedValues v.2.1 (forgetPayloadConfiguration v.1).2)
      (combinedClocks v.2.2.1 (forgetPayloadConfiguration v.1).2) k
  · rw [if_pos hk,if_pos hk]
    refine Fin.addCases (fun i => ?_) (fun j => ?_) k
    · simp only [Fin.addCases_left,mul_zero]
    · simp only [Fin.addCases_right]
  · rw [if_neg hk,if_neg hk,mul_zero]

lemma RandomizedTaggedHybridPolicy.payloadDisplacementMean_linear {n : ℕ} {T : Type}
    [MeasurableSpace T] (π : RandomizedTaggedHybridPolicy n T) (B : FiniteIntensityHybridInstance n)
    (κ : Measure T) (t0 : T) (A : ℝ × T → ℝ) {D b θ : ℝ}
    (hθ : |θ|≤ individualValueRadius D b) :
    π.payloadDisplacementMean B κ t0 (payloadValueDisplay A D b θ)=
      θ*π.payloadAmplitudeMean B κ t0 A := by
  have hg : (fun z : ℝ × T => payloadValueDisplay A D b θ z-z.1)=(fun z => θ*A z) := by
    funext z
    rw [payloadValueDisplay,if_pos hθ,add_sub_cancel_left]
  unfold RandomizedTaggedHybridPolicy.payloadDisplacementMean RandomizedTaggedHybridPolicy.payloadAmplitudeMean
  rw [hg]
  simp_rw [TaggedHybridRule.payloadSelectedAmplitude_const_mul]
  exact integral_const_mul θ _

/-- The optimized displayed value is the supremum of genuine affine payoffs
on one fixed unrestricted tagged-policy class. -/
theorem FiniteIntensityHybridInstance.poissonPayloadValuePath_value_eq_sSup {n : ℕ} {T : Type}
    [MeasurableSpace T] [StandardBorelSpace T] (B : FiniteIntensityHybridInstance n)
    (hZero : B.terminal=0) (κ : Measure T) [IsProbabilityMeasure κ] (t0 : T)
    (A : ℝ × T → ℝ) (hA : Measurable A) {D b θ : ℝ} (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ z, |A z|≤D) (hVanish : ∀ z, z.1<b → A z=0)
    (hθ : |θ|≤ individualValueRadius D b) (w c : ℝ) :
    (B.poissonPayloadValuePath κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c=
      sSup (Set.range (fun π : RandomizedTaggedHybridPolicy n T =>
        (π.sampleTags κ).scalarObjective B w c+θ*(w*π.payloadAmplitudeMean B κ t0 A))) := by
  rw [FiniteIntensityHybridInstance.poissonPayloadValuePath,
    B.optimalScalarValue_displayPoissonPayload_eq_sSup hZero κ t0 (B.cap+1) (by simp)
      (payloadValueDisplay A D b θ) (measurable_payloadValueDisplay hA D b θ)
      (B.payloadValueDisplay_supported κ hD hb hBound hVanish θ)
      (mul_nonneg (abs_nonneg θ) hD) (payloadValueDisplay_displacement_bound hD hBound θ)]
  apply congrArg sSup
  apply congrArg Set.range
  funext π
  rw [π.payloadDisplacementMean_linear B κ t0 A hθ]
  ring

end ProphetSecretary.Limiting
