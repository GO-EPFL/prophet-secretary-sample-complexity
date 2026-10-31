import ProphetSecretary.Model.LawAdaptationKernel

/-!
# Positive finite state-branch limits away from clock endpoints

The actual pending multiplier is locally constant at a root not meeting another
arrival or a unit endpoint. The continuation-state triangular law limit then
applies to that constructed multiplier.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.lawStateBranchLoss_positive_limit (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) (A : Finset (Fin n))
    (ω : World n Unit) (hxCap : ω.1 i ≤ H)
    (hPos : 0 < P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i))
    (hNotInitial : P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) ≠ c)
    (hClocks : ∀ j, j ≠ i → 1 - P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) / c ≠ ω.2.1 j) :
    let Q := P.likelihoodWidePath h hh hb hm θ
    let hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
    let d := P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)
    let m := (Q.valuePolicy hQ hw.le hc.le).rule.branchMultiplier () ω.1 ω.2.1 i A (1 - d / c)
    Tendsto (fun δ : ℝ ↦ (∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t) / δ ^ 2)
      (𝓝[≠] 0) (𝓝 (m * P.lawStateParameterDerivative h hh hb hm w θ A d ^ 2 /
        (2 * c * P.lawStateCoefficientDerivative h hh hb hm w θ A d))) := by
  let Q := P.likelihoodWidePath h hh hb hm θ
  have hQ := Q.integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hbound)
  let π : Policy Unit n := (Q.valuePolicy hQ hw.le hc.le).rule
  let d := P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)
  let m := π.branchMultiplier () ω.1 ω.2.1 i A
  let R := (P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ
  have hRB := (P.restrictTo A).likelihoodWidePath_bounded (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ
    (fun j ↦ hbound (stateEmbedding A j))
  have hR := R.integrable_maximum_of_bounded hRB
  have hLevel : optimalScalarValue R 1 0 < ω.1 i := by
    by_contra hn
    have hz := R.durationRoot_eq_zero_of_le hR (le_of_not_gt hn)
    have hd0 : d = 0 := by
      change w * R.durationRoot hR (ω.1 i) = 0
      rw [hz, mul_zero]
    exact hPos.ne' hd0
  have hr0 : 1 - d / c ≠ 0 := by
    intro hz
    have hd1 : d / c = 1 := by linarith
    have he := (div_eq_iff hc.ne').mp hd1
    exact hNotInitial (by simpa only [one_mul] using he)
  have hr1 : 1 - d / c ≠ 1 := by
    have hp := div_pos hPos hc
    intro hz
    linarith
  have hLocal := π.branchMultiplier_eventually_eq () ω.1 ω.2.1 i A hr0 hr1 hClocks
  have hLimit := (P.restrictTo A).weightedLawRootActionLoss_limit hw hc hH (fun j ↦ hbound (stateEmbedding A j)) hxCap
    (fun j ↦ h (stateEmbedding A j)) (fun j ↦ hh (stateEmbedding A j))
    (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) hθ hLevel m hLocal
  exact hLimit

end ProphetSecretary.Model
