import ProphetSecretary.Limiting.ContinuousWeightedResidual
import ProphetSecretary.Limiting.CountableMeasureSubsequence

/-!
# Actual compact extraction with a bounded aggregate continuous weight

One subsequence simultaneously extracts every ordered original marginal and
all weighted residuals. The exact residual consistency follows by weak
continuity of continuous weighting, rather than being assumed as input.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal BigOperators
namespace ProphetSecretary.Limiting

/-- One actual subsequence, chosen before all retained indices and prefix
sizes, with exact positive residual consistency. -/
theorem exists_continuousWeighted_measure_data (H C : ℝ≥0) (w : ℝ →ᵇ ℝ) (hw : ∀ x, 0 ≤ w x) (hw0 : w 0 = 0)
    (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m))
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ))
    (hWeight : ∀ m, (∑ i, ∫ x, w x ∂(P m).law i) ≤ (C : ℝ)) :
    ∃ (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ (∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ N, (ρ N).mass ≤ C) ∧ (∀ N, (ρ N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ i, Tendsto (fun m => weightOrderedPaddedLaw (P (φ m)) w i) atTop (𝓝 (Q i))) ∧
      (∀ N, Tendsto (fun m => weightOrderedResidual (P (φ m)) w N) atTop (𝓝 (ρ N))) ∧
      ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1) := by
  have hMarg (m i : ℕ) : (weightOrderedPaddedLaw (P m) w i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 :=
    weightOrderedPaddedLaw_supported_interval (P m) w H.coe_nonneg (hcap m) i
  have hMass (m N : ℕ) : (weightOrderedResidual (P m) w N).mass ≤ C :=
    by
      change ((weightOrderedResidual (P m) w N).mass : ℝ) ≤ (C : ℝ)
      exact (weightOrderedResidual_mass_le_total (P m) w hw N).trans (hWeight m)
  have hRes (m N : ℕ) : (weightOrderedResidual (P m) w N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 :=
    weightOrderedResidual_supported_interval (P m) w H.coe_nonneg (hcap m) N
  obtain ⟨Q,ρ,φ,hφ,hQ,hρmass,hρcap,hconvQ,hconvρ⟩ :=
    exists_joint_countable_marginal_residual_subsequence H.coe_nonneg
      (fun m i => weightOrderedPaddedLaw (P m) w i) hMarg (fun _ => C)
      (fun m N => weightOrderedResidual (P m) w N) hMass hRes
  refine ⟨Q,ρ,φ,hφ,hQ,hρmass,hρcap,hconvQ,hconvρ,?_⟩
  intro N
  have hsum := (continuousWeightedLaw_tendsto (hconvQ N) w hw).add (hconvρ (N+1))
  have heq : (fun m => continuousWeightedLaw (weightOrderedPaddedLaw (P (φ m)) w N) w +
      weightOrderedResidual (P (φ m)) w (N+1)) = fun m => weightOrderedResidual (P (φ m)) w N := by
    funext m
    exact (weightOrderedResidual_succ (P (φ m)) w hw hw0 N).symm
  change Tendsto (fun m => continuousWeightedLaw (weightOrderedPaddedLaw (P (φ m)) w N) w +
    weightOrderedResidual (P (φ m)) w (N+1)) atTop (𝓝 (continuousWeightedLaw (Q N) w + ρ (N+1))) at hsum
  rw [heq] at hsum
  exact tendsto_nhds_unique (hconvρ N) hsum

/-- The exact retained-prefix subtraction following extraction. All residuals
on the right are genuine positive finite measures. -/
lemma continuousWeighted_residual_prefix_identity (w : ℝ →ᵇ ℝ) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = continuousWeightedLaw (Q N) w + ρ (N+1)) (N : ℕ) :
    ρ 0 = (∑ i ∈ Finset.range N, continuousWeightedLaw (Q i) w) + ρ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,add_assoc,← hρ N]
    exact ih

end ProphetSecretary.Limiting
