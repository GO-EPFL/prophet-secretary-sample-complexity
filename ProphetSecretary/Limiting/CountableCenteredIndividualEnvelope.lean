import ProphetSecretary.Limiting.CountableCenteredIndividualTags
import ProphetSecretary.Limiting.CountableIndividualPayloadValuePath
import ProphetSecretary.Analysis.StableEnvelope

/-!
# The centered individual occurrence-tag envelope

The tag is independent and is revealed only at the affected occurrence.
Pointwise centering makes the fixed base optimizer's response zero. The
common observable policy supremum and selected-tag stability then prove a
two-sided zero derivative of the actual optimized scalar value.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal

namespace ProphetSecretary.Limiting
open CountableInstance

namespace RandomizedIndividualTaggedPolicy
variable {B : CountableInstance} {i : ℕ} {T : Type} [MeasurableSpace T]
    {κ : Measure T} [IsProbabilityMeasure κ]

lemma payloadPerturbationMean_bound (π : RandomizedIndividualTaggedPolicy B i κ)
    {A : ℝ × T → ℝ} {D : ℝ} (hBound : ∀ z, |A z|≤D) : |π.payloadPerturbationMean A|≤D := by
  have hNorm : ∀ᵐ v ∂B.completeWorldLaw (π.seedLaw.prod κ),
      ‖π.rule.individualSelectionIndicator i v*A (v.2.1 i,v.2.2.2.2)‖≤D := Eventually.of_forall (fun v => by
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (π.rule.individualSelectionIndicator_mem_unit i v).1]
    exact (mul_le_mul (π.rule.individualSelectionIndicator_mem_unit i v).2 (hBound _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  have h := norm_integral_le_of_norm_le_const hNorm
  simpa only [payloadPerturbationMean,Real.norm_eq_abs,probReal_univ,mul_one] using h

lemma payloadDisplacementMean_display (π : RandomizedIndividualTaggedPolicy B i κ)
    (A : ℝ × T → ℝ) {D b θ : ℝ} (hθ : |θ|≤ individualValueRadius D b) :
    π.payloadDisplacementMean (payloadValueDisplay A D b θ)=θ*π.payloadPerturbationMean A := by
  unfold payloadDisplacementMean payloadPerturbationMean
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by
    change π.rule.individualSelectionIndicator i v*((if |θ|≤ individualValueRadius D b then v.2.1 i+θ*A (v.2.1 i,v.2.2.2.2) else v.2.1 i)-v.2.1 i)=
      θ*(π.rule.individualSelectionIndicator i v*A (v.2.1 i,v.2.2.2.2))
    rw [if_pos hθ]
    ring)

end RandomizedIndividualTaggedPolicy

/-- The independent centered-tag version of the individual symmetric value
assertion in `lem:envelopes`. In particular fair signs times a bounded amplitude
satisfy the pointwise centering premise. -/
theorem CountableInstance.hasDerivAt_optimalScalarValue_centeredIndividualPayload
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (i : ℕ) {T : Type} [MeasurableSpace T] [StandardBorelSpace T]
    (κ : Measure T) [IsProbabilityMeasure κ] (A : ℝ × T → ℝ) (hA : Measurable A)
    {D b : ℝ} (hD : 0≤D) (hb : 0<b) (hBound : ∀ z, |A z|≤D)
    (hVanish : ∀ z, z.1<b → A z=0) (hCentered : ∀ x, (∫ t, A (x,t) ∂κ)=0) :
    HasDerivAt (fun θ => (B.individualPayloadValuePath i κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c) 0 0 := by
  let C := B.withCap (B.cap+1) (by simp)
  let π₀ := RandomizedIndividualTaggedPolicy.ignoreTag (C.valuePolicy hw hc) i κ
  let J := fun θ (π : RandomizedIndividualTaggedPolicy C i κ) => π.toBasePolicy.scalarObjective w c+
    w*π.payloadDisplacementMean (payloadValueDisplay A D b θ)
  let deriv := fun π : RandomizedIndividualTaggedPolicy C i κ => w*π.payloadPerturbationMean A
  have hRadius := individualValueRadius_pos hD hb
  have hZeroJ (π : RandomizedIndividualTaggedPolicy C i κ) : J 0 π=π.toBasePolicy.scalarObjective w c := by
    have h := π.payloadDisplacementMean_display A (show |(0 : ℝ)|≤ individualValueRadius D b by simpa only [abs_zero] using hRadius.le)
    simpa only [zero_mul,mul_zero,add_zero,J] using congrArg (fun t => π.toBasePolicy.scalarObjective w c+w*t) h
  have hBaseObjective : π₀.toBasePolicy.scalarObjective w c=C.optimalScalarValue w c :=
    (RandomizedIndividualTaggedPolicy.ignoreTag_scalarObjective (C.valuePolicy hw hc) i κ w c).trans
      (C.valuePolicy_optimal hZero hw hc)
  have hBase : ∀ π, J 0 π≤J 0 π₀ := by
    intro π
    rw [hZeroJ,hZeroJ,hBaseObjective]
    exact C.scalarObjective_le_value π.toBasePolicy w c
  have hZeroMean : π₀.payloadPerturbationMean A=0 := by
    change (∫ v : CompleteWorld (Unit × T), (C.valueRule w c).individualSelectionIndicator i (eraseCompleteSeed v)*A (v.2.1 i,v.2.2.2.2)
      ∂C.completeWorldLaw ((Measure.dirac ()).prod κ))=0
    exact C.canonical_payloadPerturbation_mean_zero hw.le hc.le i (Measure.dirac ()) κ A hA hD hBound hCentered
  have hZeroDeriv : deriv π₀=0 := by change w*π₀.payloadPerturbationMean A=0; rw [hZeroMean,mul_zero]
  have hBoundDeriv : ∀ π, |deriv π|≤w*D := by
    intro π
    change |w*π.payloadPerturbationMean A|≤_
    rw [abs_mul,abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left (π.payloadPerturbationMean_bound hBound) hw.le
  have hTaylor : ∀ θ, |θ|≤ individualValueRadius D b → ∀ π,
      |J θ π-J 0 π-θ*deriv π|≤(0 : ℝ)*θ^2 := by
    intro θ hθ π
    rw [hZeroJ]
    change |π.toBasePolicy.scalarObjective w c+w*π.payloadDisplacementMean (payloadValueDisplay A D b θ)-π.toBasePolicy.scalarObjective w c-
      θ*(w*π.payloadPerturbationMean A)|≤_
    rw [π.payloadDisplacementMean_display A hθ]
    have hEq : π.toBasePolicy.scalarObjective w c+w*(θ*π.payloadPerturbationMean A)-π.toBasePolicy.scalarObjective w c-θ*(w*π.payloadPerturbationMean A)=0 := by ring
    rw [hEq,abs_zero,zero_mul]
  obtain ⟨ψ,_,hMono,_,hLimit,hError⟩ := C.centered_payloadPerturbation_stability hZero hw hc i κ A hA hD hb hBound hVanish hCentered
  have hStable : ∀ ε, 0<ε → ∃ η, 0<η ∧ ∀ π, J 0 π₀-J 0 π≤η → |deriv π-deriv π₀|≤ε := by
    intro ε hε
    have hLimitW : Tendsto (fun r => w*ψ r) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hLimit.const_mul w
    obtain ⟨η,hηSmall,hη⟩ := ((hLimitW.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
    refine ⟨η,hη,?_⟩
    intro π hNear
    have hRegret : C.optimalScalarValue w c-π.toBasePolicy.scalarObjective w c≤η := by
      rw [hZeroJ,hZeroJ,hBaseObjective] at hNear
      exact hNear
    rw [hZeroDeriv,sub_zero]
    change |w*π.payloadPerturbationMean A|≤_
    rw [abs_mul,abs_of_pos hw]
    exact (mul_le_mul_of_nonneg_left ((hError π).trans (hMono hRegret)) hw.le).trans hηSmall.le
  have hd := ProphetSecretary.Analysis.hasDerivAt_supremum_of_stable_payoffs J deriv π₀
    (by norm_num : (0 : ℝ)≤0) (mul_nonneg hw.le hD) hRadius hBase hBoundDeriv hTaylor hStable
  have hSup (θ : ℝ) : (B.individualPayloadValuePath i κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c=sSup (Set.range (J θ)) :=
    C.optimalScalarValue_mapIndividualPayload_eq_sSup i κ (payloadValueDisplay A D b θ) (measurable_payloadValueDisplay hA D b θ)
      (B.payloadValueDisplay_supported i κ hD hb hBound hVanish θ) w c
  have hFunctions : (fun θ => sSup (Set.range (J θ)))=
      (fun θ => (B.individualPayloadValuePath i κ A hA D b hD hb hBound hVanish θ).optimalScalarValue w c) := funext (fun θ => (hSup θ).symm)
  rw [hFunctions,hZeroDeriv] at hd
  exact hd

end ProphetSecretary.Limiting
