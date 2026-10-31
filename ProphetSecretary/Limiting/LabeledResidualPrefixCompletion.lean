import ProphetSecretary.Limiting.LabeledResidualSums
import ProphetSecretary.Probability.WeakFiniteUpperRestriction

/-!
# Completing finitely many residual-prefix limits

When weak residual limits are known after a fixed finite prefix, the omitted
prefix limits follow by adding the actual remaining marginal restrictions.
All new marginals are continuity laws at the tested cutoff. Altering finitely
many prefix indices does not change the final retained-prefix limit.
-/
open MeasureTheory Set Filter
open scoped Classical Topology BigOperators
namespace ProphetSecretary.Limiting

lemma complete_residual_band_limits_from_prefix {sizes : ℕ → ℕ}
    {P : ∀ m, Model.Instance (sizes m)} {Q : ℕ → ProbabilityMeasure ℝ}
    {b : ℝ} (hb : 0≤b)
    (hQ : ∀ i, Tendsto (fun m => labeledPaddedLaw (P m) i) atTop (𝓝 (Q i)))
    (hAtom : ∀ i, (Q i : Measure ℝ) {b}=0) (K : ℕ)
    (μs : ℕ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hFirst : ∀ N, K≤N → Tendsto (fun m => labeledBandResidual (P m) N b) atTop (𝓝 (μs N)))
    (hSecond : Tendsto μs atTop (𝓝 μ)) :
    ∃ ρ : ℕ → FiniteMeasure ℝ,
      (∀ N, Tendsto (fun m => labeledBandResidual (P m) N b) atTop (𝓝 (ρ N))) ∧
      Tendsto ρ atTop (𝓝 μ) := by
  let ρ := fun N => if N<K then
    (∑ j∈Finset.range (K-N), (Q (N+j)).toFiniteMeasure.restrict (Ioi b))+μs K else μs N
  refine ⟨ρ,?_,?_⟩
  · intro N
    by_cases hNK : N<K
    · have hTerms (j : ℕ) : Tendsto
          (fun m => (labeledPaddedLaw (P m) (N+j)).toFiniteMeasure.restrict (Ioi b)) atTop
          (𝓝 ((Q (N+j)).toFiniteMeasure.restrict (Ioi b))) := by
        have hBase := ((ProbabilityMeasure.toFiniteMeasure_isEmbedding ℝ).continuous.tendsto (Q (N+j))).comp (hQ (N+j))
        exact ProphetSecretary.Probability.finite_upperRestriction_tendsto hBase b (hAtom (N+j))
      have hSum := (tendsto_finsetSum (Finset.range (K-N)) (fun j _ => hTerms j)).add (hFirst K le_rfl)
      have hEq : (fun m =>
          (∑ j∈Finset.range (K-N), (labeledPaddedLaw (P m) (N+j)).toFiniteMeasure.restrict (Ioi b))+
            labeledBandResidual (P m) K b)=fun m => labeledBandResidual (P m) N b := by
        funext m
        have h := labeledBandResidual_prefix (P m) N (K-N) hb
        rw [Nat.add_sub_of_le hNK.le] at h
        exact h.symm
      change Tendsto (fun m =>
        (∑ j∈Finset.range (K-N), (labeledPaddedLaw (P m) (N+j)).toFiniteMeasure.restrict (Ioi b))+
          labeledBandResidual (P m) K b) atTop (𝓝 (_+μs K)) at hSum
      rw [hEq] at hSum
      simpa only [ρ,if_pos hNK] using hSum
    · simpa only [ρ,if_neg hNK] using hFirst N (not_lt.mp hNK)
  · apply hSecond.congr'
    filter_upwards [eventually_ge_atTop K] with N hN
    dsimp only [ρ]
    rw [if_neg (not_lt.mpr hN)]

end ProphetSecretary.Limiting
