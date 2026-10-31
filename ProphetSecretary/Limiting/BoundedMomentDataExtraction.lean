import ProphetSecretary.Limiting.OrderedWeightedResidual
import ProphetSecretary.Limiting.CountableMeasureSubsequence

/-!
# Actual measure-data extraction under a uniform total-first-moment bound

Finite instances are genuinely permuted into decreasing mean order and padded
by zero laws. One subsequence gives every retained weak marginal limit and
every finite-prefix value-weighted residual limit. Prefix subtraction is an
exact positive-measure identity in the limit, not an assumed structure field.
This is the S≤S₀ subcase of the paper's measure extraction. The H-only case
with possible positive terminal reserve, the unweighted locally finite
Poisson intensity, and value/policy convergence remain separate obligations.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal BigOperators
namespace ProphetSecretary.Limiting

/-- One actual subsequence, chosen before all retained indices and prefix
sizes, with exact positive residual consistency. -/
theorem exists_boundedMoment_measure_data (H S₀ : ℝ≥0) (sizes : ℕ → ℕ)
    (P : ∀ m, Model.Instance (sizes m))
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x ≤ (H : ℝ))
    (hS : ∀ m, (P m).totalFirstMoment ≤ (S₀ : ℝ)) :
    ∃ (Q : ℕ → ProbabilityMeasure ℝ) (ρ : ℕ → FiniteMeasure ℝ) (φ : ℕ → ℕ),
      StrictMono φ ∧ (∀ i, (Q i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ N, (ρ N).mass ≤ S₀) ∧ (∀ N, (ρ N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0) ∧
      (∀ i, Tendsto (fun m => orderedPaddedLaw (P (φ m)) i) atTop (𝓝 (Q i))) ∧
      (∀ N, Tendsto (fun m => orderedWeightedResidual (P (φ m)) H N) atTop (𝓝 (ρ N))) ∧
      ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1) := by
  have hMarg (m i : ℕ) : (orderedPaddedLaw (P m) i : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 :=
    orderedPaddedLaw_supported_interval (P m) H.coe_nonneg (hcap m) i
  have hMass (m N : ℕ) : (orderedWeightedResidual (P m) H N).mass ≤ S₀ :=
    orderedWeightedResidual_mass_le (P m) H S₀ (hcap m) (hS m) N
  have hRes (m N : ℕ) : (orderedWeightedResidual (P m) H N : Measure ℝ) (Icc (0 : ℝ) H)ᶜ = 0 :=
    orderedWeightedResidual_supported_interval (P m) H (hcap m) N
  obtain ⟨Q,ρ,φ,hφ,hQ,hρmass,hρcap,hconvQ,hconvρ⟩ :=
    exists_joint_countable_marginal_residual_subsequence H.coe_nonneg
      (fun m i => orderedPaddedLaw (P m) i) hMarg (fun _ => S₀)
      (fun m N => orderedWeightedResidual (P m) H N) hMass hRes
  refine ⟨Q,ρ,φ,hφ,hQ,hρmass,hρcap,hconvQ,hconvρ,?_⟩
  intro N
  have hsum := (valueWeightedLaw_tendsto (hconvQ N) H).add (hconvρ (N+1))
  have heq : (fun m => valueWeightedLaw (orderedPaddedLaw (P (φ m)) N) H +
      orderedWeightedResidual (P (φ m)) H (N+1)) = fun m => orderedWeightedResidual (P (φ m)) H N := by
    funext m
    exact (orderedWeightedResidual_succ (P (φ m)) H N).symm
  change Tendsto (fun m => valueWeightedLaw (orderedPaddedLaw (P (φ m)) N) H +
    orderedWeightedResidual (P (φ m)) H (N+1)) atTop (𝓝 (valueWeightedLaw (Q N) H + ρ (N+1))) at hsum
  rw [heq] at hsum
  exact tendsto_nhds_unique (hconvρ N) hsum

/-- The exact retained-prefix subtraction following extraction. All residuals
on the right are genuine positive finite measures. -/
lemma extracted_residual_prefix_identity (H : ℝ≥0) (Q : ℕ → ProbabilityMeasure ℝ)
    (ρ : ℕ → FiniteMeasure ℝ) (hρ : ∀ N, ρ N = valueWeightedLaw (Q N) H + ρ (N+1)) (N : ℕ) :
    ρ 0 = (∑ i ∈ Finset.range N, valueWeightedLaw (Q i) H) + ρ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ,add_assoc,← hρ N]
    exact ih

end ProphetSecretary.Limiting
