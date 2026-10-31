import ProphetSecretary.Model.LawAdaptationKernel

/-!
# Vanishing initial-root branches at zero law slope

The unit-clock multiplier can jump at elapsed time zero. A zero parameter
slope makes the full unweighted triangular integral `o(h²)`; nonnegativity and
the multiplier bound by one then give the same limit for the actual branch.
-/

open MeasureTheory Set Filter
open scoped Classical Topology

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

lemma Instance.eventually_integrable_lawStateRootActionLoss (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) (A : Finset (Fin n))
    (ω : World n Unit) (hxCap : ω.1 i ≤ H)
    (hPos : 0 < P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)) :
    ∀ᶠ δ : ℝ in 𝓝 0, Integrable (ProphetSecretary.Analysis.rootActionLoss
      (P.lawStateValue h hh hb hm w (θ + δ) A) (w * ω.1 i) c
      (P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i))) volume := by
  have hCont : ContinuousAt (fun q ↦ P.lawStateRoot hbound h hh hb hm w q A (ω.1 i)) θ :=
    continuous_const.continuousAt.mul
      (((P.restrictTo A).lawDurationRoot_continuousOn hH (fun j ↦ hbound (stateEmbedding A j)) hxCap
        (fun j ↦ h (stateEmbedding A j)) (fun j ↦ hh (stateEmbedding A j))
        (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j))).continuousAt (Ioo_mem_nhds hθ.1 hθ.2))
  have hAdd : Tendsto (fun δ : ℝ ↦ θ + δ) (𝓝 0) (𝓝 θ) := by
    have hC : Continuous (fun δ : ℝ ↦ θ + δ) := continuous_const.add continuous_id
    simpa only [add_zero] using hC.tendsto 0
  filter_upwards [(hCont.tendsto.comp hAdd) (Ioi_mem_nhds hPos)] with δ hNewPos
  let Q := (P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) (θ + δ)
  have hQB := (P.restrictTo A).likelihoodWidePath_bounded (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) (θ + δ)
    (fun j ↦ hbound (stateEmbedding A j))
  have hQ := Q.integrable_maximum_of_bounded hQB
  have hLevel : optimalScalarValue Q 1 0 < ω.1 i := by
    by_contra hn
    have hz := Q.durationRoot_eq_zero_of_le hQ (le_of_not_gt hn)
    have hr0 : P.lawStateRoot hbound h hh hb hm w (θ + δ) A (ω.1 i) = 0 := by
      change w * Q.durationRoot hQ (ω.1 i) = 0
      rw [hz, mul_zero]
    exact hNewPos.ne' hr0
  have hValue : P.lawStateValue h hh hb hm w (θ + δ) A
      (P.lawStateRoot hbound h hh hb hm w (θ + δ) A (ω.1 i)) = w * ω.1 i := by
    change optimalScalarValue Q w (max 0 (w * Q.durationRoot hQ (ω.1 i))) = _
    rw [max_eq_right (mul_nonneg hw.le (Q.durationRoot_nonnegative hQ (ω.1 i)))]
    exact Q.weightedDurationRoot_value hQ hw hLevel
  rw [← hValue]
  exact ProphetSecretary.Analysis.integrable_rootActionLoss
    (P.lawStateValue_continuous hw.le hbound h hh hb hm (θ + δ) A) hc hPos hNewPos
    (fun s ↦ Q.weightedSaturatedValue_level_iff hQ hw hNewPos.le s)

/-- No continuity of the multiplier at zero elapsed time is required. -/
theorem Instance.lawStateBranchLoss_initial_limit (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) (A : Finset (Fin n))
    (ω : World n Unit) (hxCap : ω.1 i ≤ H)
    (hRoot : P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) = c)
    (hZero : P.lawStateParameterDerivative h hh hb hm w θ A c = 0) :
    Tendsto (fun δ : ℝ ↦ (∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t) / δ ^ 2)
      (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
  let d := P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i)
  have hd : 0 < d := by dsimp only [d]; rw [hRoot]; exact hc
  let R := (P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ
  have hRB := (P.restrictTo A).likelihoodWidePath_bounded (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ
    (fun j ↦ hbound (stateEmbedding A j))
  have hR := R.integrable_maximum_of_bounded hRB
  have hLevel : optimalScalarValue R 1 0 < ω.1 i := by
    by_contra hn
    have hz := R.durationRoot_eq_zero_of_le hR (le_of_not_gt hn)
    have hd0 : d = 0 := by change w * R.durationRoot hR (ω.1 i) = 0; rw [hz, mul_zero]
    exact hd.ne' hd0
  let raw := fun δ t ↦ ProphetSecretary.Analysis.rootActionLoss (P.lawStateValue h hh hb hm w (θ + δ) A) (w * ω.1 i) c d t
  have hLimit := (P.restrictTo A).weightedLawRootActionLoss_limit hw hc hH (fun j ↦ hbound (stateEmbedding A j)) hxCap
    (fun j ↦ h (stateEmbedding A j)) (fun j ↦ hh (stateEmbedding A j))
    (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) hθ hLevel (fun _ ↦ (1 : ℝ))
    (Filter.Eventually.of_forall (fun _ ↦ rfl))
  have hRawLimit : Tendsto (fun δ : ℝ ↦ (∫ t : ℝ, raw δ t) / δ ^ 2) (𝓝[≠] 0) (𝓝 (0 : ℝ)) := by
    change Tendsto (fun δ : ℝ ↦ (∫ t : ℝ, (1 : ℝ) * raw δ t) / δ ^ 2) (𝓝[≠] 0)
      (𝓝 (1 * P.lawStateParameterDerivative h hh hb hm w θ A d ^ 2 /
        (2 * c * P.lawStateCoefficientDerivative h hh hb hm w θ A d))) at hLimit
    have hz : P.lawStateParameterDerivative h hh hb hm w θ A d = 0 := by dsimp only [d]; rw [hRoot]; exact hZero
    simpa only [one_mul, hz, zero_pow (by decide : 2 ≠ 0), zero_div] using hLimit
  have hComparison : ∀ᶠ δ : ℝ in 𝓝[≠] 0,
      (∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t) / δ ^ 2 ≤
        (∫ t : ℝ, raw δ t) / δ ^ 2 := by
    filter_upwards [(P.eventually_integrable_lawStateRootActionLoss hw hc hH hbound h hh hb hm hθ i A ω hxCap hd).filter_mono nhdsWithin_le_nhds] with δ hInt
    apply div_le_div_of_nonneg_right _ (sq_nonneg δ)
    apply integral_mono (P.integrable_lawStateBranchLoss hw hc.le hH hbound h hh hb hm θ (θ + δ) i A ω) hInt
    intro t
    change _ * raw δ t ≤ raw δ t
    exact mul_le_of_le_one_left (ProphetSecretary.Analysis.rootActionLoss_nonnegative _ _ _ _ _)
      (Policy.branchMultiplier_mem_unit _ _ _ _ _ _ _).2
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [hComparison, hRawLimit (Iio_mem_nhds hε)] with δ hCmp hSmall
  have hNon : 0 ≤ (∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t) / δ ^ 2 :=
    div_nonneg (integral_nonneg (fun t ↦ P.lawStateBranchLoss_nonnegative hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t)) (sq_nonneg δ)
  simpa only [Real.dist_eq, sub_zero, abs_of_nonneg hNon] using hCmp.trans_lt hSmall

end ProphetSecretary.Model
