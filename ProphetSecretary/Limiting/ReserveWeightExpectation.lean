import ProphetSecretary.Limiting.ReserveOrderingWeight
import ProphetSecretary.Probability.BoundedContinuousIntegralMap

/-!
# The actual aggregate expectation of the reserve ordering weight

Uniform expected tail counts on the chosen bands imply aggregate weighted
mass at most one. The sum and integral interchange follows from the proved
norm-summability of continuous ramps, with no finite-support assumptions.
-/
open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Topology NNReal BigOperators Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

lemma integral_reserveBandRamp_le_tail (p : ProbabilityMeasure ℝ) (b : ℝ) :
    (∫ x, reserveBandRamp b x ∂(p : Measure ℝ)) ≤ (p : Measure ℝ).real (Ioi b) := by
  rw [← integral_indicator_one measurableSet_Ioi]
  apply integral_mono ((reserveBandRamp b).integrable _)
    ((integrable_const (1 : ℝ)).indicator measurableSet_Ioi)
  intro x
  by_cases hx : b < x
  · simpa only [Set.indicator_of_mem (show x ∈ Ioi b from hx)] using (reserveBandRamp_mem b x).2
  · rw [Set.indicator_of_notMem (show x ∉ Ioi b from hx),reserveBandRamp_zero (not_lt.mp hx)]

noncomputable def aggregateOfferIntegralCLM {n : ℕ} (P : Model.Instance n) : (ℝ →ᵇ ℝ) →L[ℝ] ℝ :=
  ∑ i, probabilityIntegralCLM (⟨P.law i,P.probability i⟩ : ProbabilityMeasure ℝ)

lemma aggregateOfferIntegralCLM_apply {n : ℕ} (P : Model.Instance n) (f : ℝ →ᵇ ℝ) :
    aggregateOfferIntegralCLM P f = ∑ i, ∫ x, f x ∂P.law i := by
  simp only [aggregateOfferIntegralCLM,_root_.sum_apply,probabilityIntegralCLM_apply]
  rfl

/-- Uniform in the number of finite input variables. -/
theorem sum_integral_reserveOrderingWeight_le_one {n : ℕ} (P : Model.Instance n)
    (b : ℕ → ℝ) (B : ℕ → ℝ≥0) (hB : ∀ k, 1 ≤ B k)
    (htail : ∀ k, extendedTailCount P (b k) ≤ (B k : ENNReal)) :
    (∑ i, ∫ x, reserveOrderingWeight b B x ∂P.law i) ≤ 1 := by
  have hsum := (aggregateOfferIntegralCLM P).hasSum (summable_reserveWeightTerm b B hB).hasSum
  have hterm (k : ℕ) : aggregateOfferIntegralCLM P (reserveWeightTerm b B k) ≤ (1/2 : ℝ)^(k+1) := by
    rw [aggregateOfferIntegralCLM_apply]
    change (∑ i, ∫ x, reserveWeightCoefficient B k * reserveBandRamp (b k) x ∂P.law i) ≤ _
    simp_rw [integral_const_mul]
    rw [← Finset.mul_sum]
    have htailReal : P.tailCount (b k) ≤ (B k : ℝ) := by
      rw [← extendedTailCount_toReal]
      exact ENNReal.toReal_mono ENNReal.coe_ne_top (htail k)
    have hRamp : (∑ i, ∫ x, reserveBandRamp (b k) x ∂P.law i) ≤ (B k : ℝ) := by
      apply le_trans _ htailReal
      exact Finset.sum_le_sum fun i _ => integral_reserveBandRamp_le_tail
        (⟨P.law i,P.probability i⟩ : ProbabilityMeasure ℝ) (b k)
    have hpos : (0 : ℝ) < B k := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (hB k)
    calc
      _ ≤ reserveWeightCoefficient B k * B k := mul_le_mul_of_nonneg_left hRamp (reserveWeightCoefficient_nonneg B k)
      _ = (1/2 : ℝ)^(k+1) := div_mul_cancel₀ _ hpos.ne'
  rw [← aggregateOfferIntegralCLM_apply,reserveOrderingWeight,← hsum.tsum_eq,← tsum_reserve_geometric]
  exact hsum.summable.tsum_le_tsum hterm summable_reserve_geometric

end ProphetSecretary.Limiting
