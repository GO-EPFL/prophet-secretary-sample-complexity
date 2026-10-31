import ProphetSecretary.Limiting.CountableWeightSlope

/-!
# The full-policy scalar-weight envelope

The common admissible policy class is independent of scalar weights. Its
payoffs are exactly affine, and the proved outcome stability makes the fixed
policy slopes continuous at small base regret. The resulting derivative of
the reoptimized value is therefore the base optimizer's R−T.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting.CountableInstance

theorem hasDerivAt_optimalScalarValue_weight (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) :
    HasDerivAt (fun θ => B.optimalScalarValue (w+θ) (c-θ))
      (B.valuePolicy hw hc).expectedWeightSlope 0 := by
  let π0 := B.valuePolicy hw hc
  let J := fun θ (π : RandomizedCountablePolicy B) => π.scalarObjective (w+θ) (c-θ)
  let D := fun π : RandomizedCountablePolicy B => π.expectedWeightSlope
  have hZeroJ (π : RandomizedCountablePolicy B) : J 0 π=π.scalarObjective w c := by
    simp only [J,add_zero,sub_zero]
  have hBase : ∀ π, J 0 π≤J 0 π0 := by
    intro π
    rw [hZeroJ,hZeroJ]
    exact (B.scalarObjective_le_value π w c).trans_eq (B.valuePolicy_optimal hZero hw hc).symm
  have hD : ∀ π, |D π|≤(B.cap : ℝ)+1 := fun π => π.expectedWeightSlope_abs_le
  have hTaylor : ∀ θ : ℝ, |θ|≤1 → ∀ π,
      |J θ π-J 0 π-θ*D π|≤(0 : ℝ)*θ^2 := by
    intro θ _hθ π
    have hEq : J θ π-J 0 π-θ*D π=0 := by
      dsimp only [J,D,RandomizedCountablePolicy.expectedWeightSlope,RandomizedCountablePolicy.scalarObjective]
      ring
    rw [hEq,abs_zero,zero_mul]
  obtain ⟨Ω,_hΩ,hMono,_hΩZero,hLimit,hError⟩ := B.outcome_stability hZero hw hc
  have hStable : ∀ eps : ℝ, 0<eps → ∃ eta : ℝ, 0<eta ∧
      ∀ π, J 0 π0-J 0 π≤eta → |D π-D π0|≤eps := by
    intro eps hEps
    obtain ⟨eta,hSmall,hEta⟩ := ((hLimit.eventually (gt_mem_nhds hEps)).and self_mem_nhdsWithin).exists
    refine ⟨eta,hEta,?_⟩
    intro π hNear
    have hRegret : B.optimalScalarValue w c-π.scalarObjective w c≤eta := by
      rw [hZeroJ,hZeroJ,B.valuePolicy_optimal hZero hw hc] at hNear
      exact hNear
    exact (π.expectedWeightSlope_difference_le hw hc).trans
      ((hError π).trans ((hMono hRegret).trans hSmall.le))
  have hDeriv := ProphetSecretary.Analysis.hasDerivAt_supremum_of_stable_payoffs J D π0
    (by norm_num : (0 : ℝ)≤0) (by positivity : 0≤(B.cap : ℝ)+1) (by norm_num : (0 : ℝ)<1)
    hBase hD hTaylor hStable
  exact hDeriv

end ProphetSecretary.Limiting.CountableInstance
