import ProphetSecretary.Limiting.WeightedBandPoissonState
import ProphetSecretary.Limiting.CountablePrefixState
import ProphetSecretary.Limiting.WeakHybridValue

/-!
# The original-sequence limit at a fixed retained prefix and cutoff

Both N and b are fixed before taking this limit. Original ordered marginal
laws and actual upper-band residual measures are the weak-convergence inputs.
The scalar conclusion concerns all admissible hybrid policies.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped BigOperators Classical NNReal Topology

namespace ProphetSecretary.Limiting

lemma weightOrderedBandState_uniform_weak (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (wgt : ℝ →ᵇ ℝ) (N : ℕ) (b W : ℝ≥0) (hbH : b ≤ B.cap)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (B.cap : ℝ))
    (μ : FiniteMeasure ℝ) (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap)
    (hIndividuals : ∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P m) wgt i) atTop (𝓝 (B.individuals i)))
    (hIntensity : Tendsto (fun m => weightOrderedBandResidual (P m) wgt N b) atTop (𝓝 μ)) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop, ∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c →
      |(weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).optimalScalarValue w c-
        (B.prefixIntensityState N b hbH μ hμ).optimalScalarValue w c| < ε := by
  let Bs := fun m => weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)
  let D := B.prefixIntensityState N b hbH μ hμ
  have hP : ∀ i : Fin N, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (D.individuals.marginalProbabilityLaw i)) := by
    intro i
    have hs : (fun m => (Bs m).individuals.marginalProbabilityLaw i) =
        (fun m => weightOrderedPaddedLaw (P m) wgt i.val) := by
      funext m
      exact weightOrderedPrefix_marginalProbabilityLaw (P m) wgt N i
    rw [hs]
    have he : D.individuals.marginalProbabilityLaw i = B.individuals i.val :=
      B.individualPrefix_marginalProbabilityLaw N i
    rw [he]
    exact hIndividuals i.val
  have hμs : Tendsto (fun m => (Bs m).intensity) atTop (𝓝 D.intensity) := by
    have he : (fun m => (Bs m).intensity) = fun m => weightOrderedBandResidual (P m) wgt N b := by
      funext m
      exact weightOrderedBandState_intensity (P m) wgt N B.cap b hbH (hcap m)
    rw [he]
    exact hIntensity
  exact optimalScalarValue_uniform_weak Bs D B.cap W (fun _ => le_rfl) le_rfl (fun _ => rfl) hP hμs

lemma weightOrderedBandState_expectedMaximum_tendsto (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (wgt : ℝ →ᵇ ℝ) (N : ℕ) (b : ℝ≥0) (hbH : b ≤ B.cap)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (B.cap : ℝ))
    (μ : FiniteMeasure ℝ) (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap)
    (hIndividuals : ∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P m) wgt i) atTop (𝓝 (B.individuals i)))
    (hIntensity : Tendsto (fun m => weightOrderedBandResidual (P m) wgt N b) atTop (𝓝 μ)) :
    Tendsto (fun m => (weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)).expectedMaximum) atTop
      (𝓝 (B.prefixIntensityState N b hbH μ hμ).expectedMaximum) := by
  let Bs := fun m => weightOrderedBandState (P m) wgt N B.cap b hbH (hcap m)
  let D := B.prefixIntensityState N b hbH μ hμ
  have hP : ∀ i : Fin N, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (D.individuals.marginalProbabilityLaw i)) := by
    intro i
    have hs : (fun m => (Bs m).individuals.marginalProbabilityLaw i) =
        (fun m => weightOrderedPaddedLaw (P m) wgt i.val) := by
      funext m
      exact weightOrderedPrefix_marginalProbabilityLaw (P m) wgt N i
    rw [hs]
    have he : D.individuals.marginalProbabilityLaw i = B.individuals i.val :=
      B.individualPrefix_marginalProbabilityLaw N i
    rw [he]
    exact hIndividuals i.val
  have hμs : Tendsto (fun m => (Bs m).intensity) atTop (𝓝 D.intensity) := by
    have he : (fun m => (Bs m).intensity) = fun m => weightOrderedBandResidual (P m) wgt N b := by
      funext m
      exact weightOrderedBandState_intensity (P m) wgt N B.cap b hbH (hcap m)
    rw [he]
    exact hIntensity
  exact expectedMaximum_tendsto_of_weak Bs D B.cap (fun _ => le_rfl) le_rfl (fun _ => rfl) hP hμs

end ProphetSecretary.Limiting
