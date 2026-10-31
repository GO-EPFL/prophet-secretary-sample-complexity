import ProphetSecretary.Limiting.CountableIndividualPerturbationTag
import ProphetSecretary.Limiting.CountableIndividualValuePath
import ProphetSecretary.Analysis.StableEnvelope

/-!
# The individual value-perturbation envelope

The two causal simulations identify the full policy supremum with a common
base-observation class. Each fixed policy has an exact linear selected-value
response. Selected-occurrence stability then identifies the derivative using
the fixed base-optimal policy.
-/

open MeasureTheory Set Filter
open scoped Classical Topology NNReal

namespace ProphetSecretary.Limiting
open CountableInstance

lemma RandomizedCountablePolicy.individualPerturbationMean_bound {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) {φ : ℝ → ℝ} {D : ℝ} (_hD : 0≤D) (hBound : ∀ x, |φ x|≤D) :
    |π.individualPerturbationMean i φ|≤D := by
  have hNorm : ∀ᵐ v ∂B.completeWorldLaw π.seedLaw, ‖π.rule.individualSelectionIndicator i v*φ (v.2.1 i)‖≤D :=
    Eventually.of_forall (fun v => by
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (π.rule.individualSelectionIndicator_mem_unit i v).1]
      exact (mul_le_mul (π.rule.individualSelectionIndicator_mem_unit i v).2 (hBound _) (abs_nonneg _) zero_le_one).trans_eq (one_mul _))
  have h := norm_integral_le_of_norm_le_const hNorm
  simpa only [RandomizedCountablePolicy.individualPerturbationMean,Real.norm_eq_abs,probReal_univ,mul_one] using h

lemma RandomizedCountablePolicy.individualDisplacementMean_display {B : CountableInstance}
    (π : RandomizedCountablePolicy B) (i : ℕ) (φ : ℝ → ℝ) {D b θ : ℝ}
    (hθ : |θ|≤ individualValueRadius D b) :
    π.individualDisplacementMean i (individualValueDisplay φ D b θ)=θ*π.individualPerturbationMean i φ := by
  unfold RandomizedCountablePolicy.individualDisplacementMean RandomizedCountablePolicy.individualPerturbationMean
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Eventually.of_forall (fun v => by
    change π.rule.individualSelectionIndicator i v*((if |θ|≤ individualValueRadius D b then v.2.1 i+θ*φ (v.2.1 i) else v.2.1 i)-v.2.1 i)=θ*(π.rule.individualSelectionIndicator i v*φ (v.2.1 i))
    rw [if_pos hθ]
    ring)

/-- The individual-variable value-perturbation assertion of `lem:envelopes`.
Measurability, a uniform bound and vanishing below a positive level suffice;
in particular the assertion applies to the stated bounded continuous maps. -/
theorem CountableInstance.hasDerivAt_optimalScalarValue_individualValuePath
    (B : CountableInstance) (hZero : B.terminal=0) {w c : ℝ} (hw : 0<w) (hc : 0<c)
    (i : ℕ) (φ : ℝ → ℝ) (hφ : Measurable φ) {D b : ℝ} (hD : 0≤D) (hb : 0<b)
    (hBound : ∀ x, |φ x|≤D) (hVanish : ∀ x, x<b → φ x=0) :
    HasDerivAt (fun θ => (B.individualValuePath i φ hφ D b hD hb hBound hVanish θ).optimalScalarValue w c)
      (w*(B.valuePolicy hw hc).individualPerturbationMean i φ) 0 := by
  let C := B.withCap (B.cap+1) (by simp)
  let π₀ := C.valuePolicy hw hc
  let J := fun θ (π : RandomizedCountablePolicy C) => π.scalarObjective w c+
    w*π.individualDisplacementMean i (individualValueDisplay φ D b θ)
  let deriv := fun π : RandomizedCountablePolicy C => w*π.individualPerturbationMean i φ
  have hRadius := individualValueRadius_pos hD hb
  have hZeroJ (π : RandomizedCountablePolicy C) : J 0 π=π.scalarObjective w c := by
    have h := π.individualDisplacementMean_display i φ (show |(0 : ℝ)|≤ individualValueRadius D b by simpa only [abs_zero] using hRadius.le)
    simpa only [zero_mul,mul_zero,add_zero,J] using congrArg (fun t => π.scalarObjective w c+w*t) h
  have hBase : ∀ π, J 0 π≤J 0 π₀ := by
    intro π
    rw [hZeroJ,hZeroJ]
    exact (C.scalarObjective_le_value π w c).trans_eq (C.valuePolicy_optimal hZero hw hc).symm
  have hDerivBound : ∀ π, |deriv π|≤w*D := by
    intro π
    change |w*π.individualPerturbationMean i φ|≤_
    rw [abs_mul,abs_of_pos hw]
    exact mul_le_mul_of_nonneg_left (π.individualPerturbationMean_bound i hD hBound) hw.le
  have hTaylor : ∀ θ, |θ|≤ individualValueRadius D b → ∀ π,
      |J θ π-J 0 π-θ*deriv π|≤(0 : ℝ)*θ^2 := by
    intro θ hθ π
    rw [hZeroJ]
    change |π.scalarObjective w c+w*π.individualDisplacementMean i (individualValueDisplay φ D b θ)-π.scalarObjective w c-θ*(w*π.individualPerturbationMean i φ)|≤_
    rw [π.individualDisplacementMean_display i φ hθ]
    have hEq : π.scalarObjective w c+w*(θ*π.individualPerturbationMean i φ)-π.scalarObjective w c-θ*(w*π.individualPerturbationMean i φ)=0 := by ring
    rw [hEq,abs_zero,zero_mul]
  obtain ⟨ψ,_,hMono,_,hLimit,hError⟩ := C.individualPerturbationMean_stability hZero hw hc i hφ hD hb hBound hVanish
  have hStable : ∀ ε, 0<ε → ∃ η, 0<η ∧ ∀ π, J 0 π₀-J 0 π≤η → |deriv π-deriv π₀|≤ε := by
    intro ε hε
    have hLimitW : Tendsto (fun r => w*ψ r) (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hLimit.const_mul w
    obtain ⟨η,hηSmall,hη⟩ := ((hLimitW.eventually (gt_mem_nhds hε)).and self_mem_nhdsWithin).exists
    refine ⟨η,hη,?_⟩
    intro π hNear
    have hRegret : C.optimalScalarValue w c-π.scalarObjective w c≤η := by
      rw [hZeroJ,hZeroJ,C.valuePolicy_optimal hZero hw hc] at hNear
      exact hNear
    change |w*π.individualPerturbationMean i φ-w*π₀.individualPerturbationMean i φ|≤_
    rw [← mul_sub,abs_mul,abs_of_pos hw]
    exact (mul_le_mul_of_nonneg_left ((hError π).trans (hMono hRegret)) hw.le).trans hηSmall.le
  have hd := ProphetSecretary.Analysis.hasDerivAt_supremum_of_stable_payoffs J deriv π₀
    (by norm_num : (0 : ℝ)≤0) (mul_nonneg hw.le hD) hRadius hBase hDerivBound hTaylor hStable
  have hSup (θ : ℝ) : (B.individualValuePath i φ hφ D b hD hb hBound hVanish θ).optimalScalarValue w c=
      sSup (Set.range (J θ)) := C.optimalScalarValue_mapIndividual_eq_sSup i
        (individualValueDisplay φ D b θ) (measurable_individualValueDisplay hφ D b θ)
        (B.individualValueDisplay_supported i hD hb hBound hVanish θ) w c
  have hFunctions : (fun θ => sSup (Set.range (J θ)))=
      (fun θ => (B.individualValuePath i φ hφ D b hD hb hBound hVanish θ).optimalScalarValue w c) := funext (fun θ => (hSup θ).symm)
  rw [hFunctions] at hd
  have hCoeff : deriv π₀=w*(B.valuePolicy hw hc).individualPerturbationMean i φ := by
    change w*(∫ v, (C.valueRule w c).individualSelectionIndicator i v*φ (v.2.1 i) ∂C.completeWorldLaw (Measure.dirac ()))=_
    dsimp only [C]
    rw [B.withCap_valueRule (B.cap+1) (by simp)]
    rfl
  rw [hCoeff] at hd
  exact hd

end ProphetSecretary.Limiting
