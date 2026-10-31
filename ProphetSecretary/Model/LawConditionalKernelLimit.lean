import ProphetSecretary.Model.LawBranchKernelLimit
import ProphetSecretary.Model.LawEndpointRegularity
import ProphetSecretary.Reach.CrossingNull

/-! # Conditional law-regret limits for actual finite instances
The finite state partition is combined before integrating residual offers and
clocks. Exceptional initial-level slopes and clock/root coincidences are
removed using the actual product law.
-/
open MeasureTheory Set Filter
open scoped Topology BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma Instance.lawStateRoot_value (P : Instance n) {w H : ℝ} (hw : 0 < w)
    (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    (θ : ℝ) (A : Finset (Fin n)) (x : ℝ)
    (hd : 0 < P.lawStateRoot hbound h hh hb hm w θ A x) :
    optimalScalarValue ((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
      (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
      (fun j ↦ hm (stateEmbedding A j)) θ) w
      (P.lawStateRoot hbound h hh hb hm w θ A x) = w * x := by
  let Q := (P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ
  have hQB := (P.restrictTo A).likelihoodWidePath_bounded (fun j ↦ h (stateEmbedding A j))
    (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j)) (fun j ↦ hm (stateEmbedding A j)) θ
    (fun j ↦ hbound (stateEmbedding A j))
  have hQ := Q.integrable_maximum_of_bounded hQB
  have hx : optimalScalarValue Q 1 0 < x := by
    by_contra hn
    have hz := Q.durationRoot_eq_zero_of_le hQ (le_of_not_gt hn)
    have hr0 : P.lawStateRoot hbound h hh hb hm w θ A x = 0 := by
      change w * Q.durationRoot hQ x = 0
      rw [hz, mul_zero]
    exact hd.ne' hr0
  exact Q.weightedDurationRoot_value hQ hw hx

theorem Instance.lawConditionalRegret_kernel_limit (P : Instance n) {w c H : ℝ}
    (hw : 0 < w) (hc : 0 < c) (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ a ∂P.law i, a ≤ H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ a ∂P.law i, |h i a| ≤ 1) (hm : ∀ i, ∫ a, h i a ∂P.law i = 0)
    {θ : ℝ} (hθ : θ ∈ Ioo (-(1 / 2) : ℝ) (1 / 2)) (i : Fin n) (ω : World n Unit)
    (hx : 0 ≤ ω.1 i) (hxCap : ω.1 i ≤ H) (hClocks : ∀ j, ω.2.1 j < 1)
    (hNoTie : ∀ (A : Finset (Fin n)) j, j ≠ i →
      1 - P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) / c ≠ ω.2.1 j)
    (hInitial : ∀ A : Finset (Fin n),
      optimalScalarValue ((P.restrictTo A).likelihoodWidePath (fun j ↦ h (stateEmbedding A j))
        (fun j ↦ hh (stateEmbedding A j)) (fun j ↦ hb (stateEmbedding A j))
        (fun j ↦ hm (stateEmbedding A j)) θ) w c = w * ω.1 i →
      P.lawStateParameterDerivative h hh hb hm w θ A c = 0) :
    Tendsto (fun δ : ℝ ↦ P.lawConditionalRegret hw hc.le hbound h hh hb hm θ (θ + δ) i ω / δ ^ 2)
      (𝓝[≠] 0) (𝓝 ((∑ A : Finset (Fin n), P.lawAdaptationKernel hw hc.le hbound h hh hb hm θ i A ω) / 2)) := by
  have hL := tendsto_finsetSum Finset.univ (fun A _ ↦
    P.lawStateBranchLoss_kernel_limit hw hc hH hbound h hh hb hm hθ i A ω hx hxCap hClocks
      (hNoTie A) (fun he ↦ hInitial A (by
        have hp : 0 < P.lawStateRoot hbound h hh hb hm w θ A (ω.1 i) := by rw [he]; exact hc
        simpa only [he] using P.lawStateRoot_value hw hbound h hh hb hm θ A (ω.1 i) hp)))
  have heq (δ : ℝ) : P.lawConditionalRegret hw hc.le hbound h hh hb hm θ (θ + δ) i ω / δ ^ 2 =
      ∑ A : Finset (Fin n), (∫ t : ℝ, P.lawStateBranchLoss hw hc.le hbound h hh hb hm θ (θ + δ) i A ω t) / δ ^ 2 := by
    rw [P.lawConditionalRegret_eq_sum_stateBranchIntegrals hw hc hH hbound h hh hb hm θ (θ + δ) i ω, Finset.sum_div]
  simpa only [← heq, ← Finset.sum_div] using hL

end ProphetSecretary.Model
