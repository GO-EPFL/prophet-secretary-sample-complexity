import ProphetSecretary.Limiting.HybridSelectedTagBounds
import ProphetSecretary.Limiting.HybridFixedWeightStability

/-!
# Uniform selected-occurrence stability in finite-intensity hybrids

This is the finite-intensity component of `cor:selected-occurrence`. A common
bounded measurable tag assignment vanishes below a fixed positive offer level.
The modulus is uniform over retained dimensions, anonymous intensities and
all actual randomized competitors under a common positive-tail profile.
-/
open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.Limiting

theorem finite_hybrid_selectedOccurrence_stability_with_profile {α : Type*} (n : α → ℕ)
    (B : ∀ a, FiniteIntensityHybridInstance (n a)) {H δ D b : ℝ}
    (hH : 0 ≤ H) (hδ : 0 < δ) (hD : 0 ≤ D) (hb : 0 < b)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ) ≤ H)
    (L : ℝ → ℝ) (hL : ∀ d, 0 < d → 0 ≤ L d)
    (hTail : ∀ a d, 0 < d → (B a).tailCount d ≤ L d) :
    ∃ ψ : ℝ → ℝ, (∀ t, 0 ≤ ψ t) ∧ Monotone ψ ∧ ψ 0=0 ∧
      Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ a w c, δ ≤ w → δ ≤ c → w+c=1 → ∀ π : RandomizedHybridPolicy (n a),
        ∀ tag : HybridTags (n a) π.Seed, tag.IsMeasurable →
        (∀ᵐ v ∂(B a).law π.seedLaw, ∀ k, |tag v k| ≤ D) →
        (∀ᵐ v ∂(B a).law π.seedLaw, ∀ k, combinedValues v.2.1 v.1.2 k < b → tag v k=0) →
        π.expectedSelectedTagError (B a) w c tag ≤
          ψ ((B a).optimalScalarValue w c-π.scalarObjective (B a) w c) := by
  obtain ⟨ω,hω,hMono,hZero,hLim,hError,_hNeg⟩ :=
    finite_hybrid_outcome_stability_with_profile n B hH hδ ha hCap L hL hTail
  let ψ : ℝ → ℝ := fun r => Model.selectedTagErrorBound D b (1+L (b/2)) (ω r)
  refine ⟨ψ,(fun r => Model.selectedTagErrorBound_nonnegative hD hb (hω r).1),
    (Model.selectedTagErrorBound_monotone hD hb).comp hMono,?_,?_,?_⟩
  · dsimp only [ψ]
    rw [hZero,Model.selectedTagErrorBound_zero]
  · exact Model.selectedTagErrorBound_tendsto_zero hLim D b (1+L (b/2))
  · intro a w c hw hc hSum π tag hTag hBound hTagZero
    exact π.selectedTag_stability_of_outcome_bound (B a) (hδ.le.trans hw) (hδ.le.trans hc) hD hb
      (hTail a (b/2) (by positivity)) (hError a w c hw hc hSum π) tag hTag hBound hTagZero

theorem finite_hybrid_selectedOccurrence_stability_fixed_weights {α : Type*} (n : α → ℕ)
    (B : ∀ a, FiniteIntensityHybridInstance (n a)) {H w c D b : ℝ}
    (hH : 0 ≤ H) (hw : 0 < w) (hc : 0 < c) (hD : 0 ≤ D) (hb : 0 < b)
    (ha : ∀ a, (B a).terminal=0) (hCap : ∀ a, ((B a).cap : ℝ) ≤ H)
    (L : ℝ → ℝ) (hL : ∀ d, 0 < d → 0 ≤ L d)
    (hTail : ∀ a d, 0 < d → (B a).tailCount d ≤ L d) :
    ∃ ψ : ℝ → ℝ, (∀ t, 0 ≤ ψ t) ∧ Monotone ψ ∧ ψ 0=0 ∧
      Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      ∀ a (π : RandomizedHybridPolicy (n a)),
        ∀ tag : HybridTags (n a) π.Seed, tag.IsMeasurable →
        (∀ᵐ v ∂(B a).law π.seedLaw, ∀ k, |tag v k| ≤ D) →
        (∀ᵐ v ∂(B a).law π.seedLaw, ∀ k, combinedValues v.2.1 v.1.2 k < b → tag v k=0) →
        π.expectedSelectedTagError (B a) w c tag ≤
          ψ ((B a).optimalScalarValue w c-π.scalarObjective (B a) w c) := by
  obtain ⟨ω,hω,hMono,hZero,hLim,hError,_hNeg⟩ :=
    finite_hybrid_outcome_stability_fixed_weights n B hH hw hc ha hCap L hL hTail
  let ψ : ℝ → ℝ := fun r => Model.selectedTagErrorBound D b (1+L (b/2)) (ω r)
  refine ⟨ψ,(fun r => Model.selectedTagErrorBound_nonnegative hD hb (hω r).1),
    (Model.selectedTagErrorBound_monotone hD hb).comp hMono,?_,?_,?_⟩
  · dsimp only [ψ]
    rw [hZero,Model.selectedTagErrorBound_zero]
  · exact Model.selectedTagErrorBound_tendsto_zero hLim D b (1+L (b/2))
  · intro a π tag hTag hBound hTagZero
    exact π.selectedTag_stability_of_outcome_bound (B a) hw.le hc.le hD hb
      (hTail a (b/2) (by positivity)) (hError a π) tag hTag hBound hTagZero

end ProphetSecretary.Limiting
