import ProphetSecretary.Model.LawRegularBranchLimit
import ProphetSecretary.Model.LawInitialBranches
import ProphetSecretary.Model.LawTerminalBranches

/-!
# Statewise law adaptation limits

Positive interior crossings contribute the directional adaptation kernel.
Terminal branches vanish by the observed finite clock history. Initial branches
vanish when their fixed-coefficient law derivative is zero.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

theorem Instance.lawStateBranchLoss_kernel_limit (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) (A : Finset (Fin n))
    (ω : World n Unit) (hx : 0 ≤ ω.1 i) (hxCap : ω.1 i ≤ H) (hClocks : ∀ j, ω.2.1 j < 1)
    (hNoTie : ∀ j, j ≠ i → 1 - P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) / c ≠ ω.2.1 j)
    (hInitial : P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) = c →
      P.lawStateParameterDerivative h hh hb hm w θ A c = 0) :
    Tendsto (fun δ : ℝ ↦ (∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t) / δ ^ 2)
      (𝓝[≠] 0) (𝓝 (P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω / 2)) := by
  let d := P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)
  have hd : 0 ≤ d := mul_nonneg hw.le ((P.restrictTo A).lawDurationRoot_nonnegative
    (fun j ↦ hbound (stateEmbedding A j)) (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
    (fun j ↦ hm (stateEmbedding A j)) θ (ω.1 i))
  by_cases hz : d = 0
  · have hL := P.lawStateBranchLoss_terminal_limit hw hc hH hbound h hh hb hm hθ i A ω hx hxCap hClocks hz
    have hzRoot : P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) = 0 := hz
    simpa only [Instance.lawAdaptationKernel, hzRoot, lt_self_iff_false, false_and, ite_false, zero_div] using hL
  have hp : 0 < d := lt_of_le_of_ne hd (Ne.symm hz)
  by_cases hi : d = c
  · have hL := P.lawStateBranchLoss_initial_limit hw hc hH hbound h hh hb hm hθ i A ω hxCap hi (hInitial hi)
    have hiRoot : P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) = c := hi
    simpa only [Instance.lawAdaptationKernel, hiRoot, lt_self_iff_false, and_false, ite_false, zero_div] using hL
  have hL := P.lawStateBranchLoss_positive_limit hw hc hH hbound h hh hb hm hθ i A ω hxCap hp hi hNoTie
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
  let m := π.branchMultiplier () ω.1 ω.2.1 i A (1 - d / c)
  change Tendsto _ _ (𝓝 (m * P.lawStateParameterDerivative h hh hb hm w θ A d ^ 2 /
    (2 * c * P.lawStateCoefficientDerivative h hh hb hm w θ A d))) at hL
  have hEq : P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω / 2 =
      m * P.lawStateParameterDerivative h hh hb hm w θ A d ^ 2 /
        (2 * c * P.lawStateCoefficientDerivative h hh hb hm w θ A d) := by
    change (if 0 < d ∧ d < c then m * _ / (c * _) else 0) / 2 = _
    by_cases hdc : d < c
    · rw [if_pos ⟨hp, hdc⟩]
      ring
    · have hdc' : c < d := lt_of_le_of_ne (le_of_not_gt hdc) (Ne.symm hi)
      have hr : 1 - d / c < 0 := by
        have hRatio : (1 : ℝ) < d / c := (lt_div_iff₀ hc).2 (by simpa only [one_mul] using hdc')
        linarith
      have hm0 : m = 0 := π.branchMultiplier_zero_off_unit () ω.1 ω.2.1 i A
        (fun ht ↦ (not_le_of_gt hr) ht.1)
      rw [if_neg (fun ht ↦ hdc ht.2), hm0, zero_mul, zero_div, zero_div]
  rw [hEq]
  exact hL

end ProphetSecretary.Model
