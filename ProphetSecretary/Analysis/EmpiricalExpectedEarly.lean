import ProphetSecretary.Analysis.EmpiricalExpectedNear
import ProphetSecretary.Analysis.EmpiricalDyadicLoss
import Mathlib.Topology.Algebra.InfiniteSum.Order

/-!
# Averaging and summing the early-band losses

The actual weighted sixth-moment profile at entrance 2a turns a time loss
CBE⁶/a⁵ into an explicit inverse-power rate. A nonnegative family dominated
by these rates is summable, with a dimension-free bound after dyadic summation.
-/

open MeasureTheory Filter
open scoped BigOperators

namespace ProphetSecretary.Analysis

theorem empirical_expected_early_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {F W : Ω → ℝ} (hm : AEStronglyMeasurable F μ) (hF0 : ∀ᵐ ω ∂μ, 0 ≤ F ω)
    (hW : Integrable W μ) {k a C C₆ S hi : ℝ}
    (hk : 0 < k) (ha : 0 < a) (hC : 0 ≤ C) (hC₆ : 0 ≤ C₆) (hS : 0 ≤ S) (hhi : 0 < hi)
    (hdom : ∀ᵐ ω ∂μ, F ω ≤ (C / a ^ 5) * W ω)
    (hmoment : (∫ ω, W ω ∂μ) ≤ C₆ * ((2 * a) ^ 3 / k ^ 3 + 1 / k ^ 6) * (2 * a * (1 + S) / hi)) :
    Integrable F μ ∧ (∫ ω, F ω ∂μ) ≤
      (16 * C * C₆ / hi) * (1 + S) * (1 / (a * k ^ 3) + 1 / (a ^ 4 * k ^ 6)) := by
  have hbase := integral_nonnegative_le_scaled μ hm hF0 hW hdom
  refine ⟨hbase.1, hbase.2.trans ?_⟩
  have hmom := mul_le_mul_of_nonneg_left hmoment (div_nonneg hC (pow_nonneg ha.le 5))
  have heq : (C / a ^ 5) * (C₆ * ((2 * a) ^ 3 / k ^ 3 + 1 / k ^ 6) * (2 * a * (1 + S) / hi)) =
      ((C * C₆ / hi) * (1 + S)) * (16 * (1 / (a * k ^ 3)) + 2 * (1 / (a ^ 4 * k ^ 6))) := by
    field_simp
    ring
  rw [heq] at hmom
  have hn : 0 ≤ 1 / (a ^ 4 * k ^ 6) := by positivity
  have hbudget : 16 * (1 / (a * k ^ 3)) + 2 * (1 / (a ^ 4 * k ^ 6)) ≤
      16 * (1 / (a * k ^ 3) + 1 / (a ^ 4 * k ^ 6)) := by nlinarith only [hn]
  have hs := mul_le_mul_of_nonneg_left hbudget (by positivity : 0 ≤ (C * C₆ / hi) * (1 + S))
  have h := hmom.trans hs
  have hend : ((C * C₆ / hi) * (1 + S)) * (16 * (1 / (a * k ^ 3) + 1 / (a ^ 4 * k ^ 6))) =
      (16 * C * C₆ / hi) * (1 + S) * (1 / (a * k ^ 3) + 1 / (a ^ 4 * k ^ 6)) := by ring
  exact h.trans_eq hend

/-- Summing actual nonnegative band expectations introduces no band-count
factor. The initial level a may exceed x by any fixed scalar-interval factor. -/
theorem empirical_early_rates_summable {L : ℕ → ℝ} {D a k x : ℝ}
    (hk : 0 < k) (hxk : 1 / k ≤ x) (hxa : x ≤ a) (hD : 0 ≤ D)
    (hL0 : ∀ j, 0 ≤ L j)
    (hbound : ∀ j, L j ≤ D * (1 / (((2 : ℝ) ^ j * a) * k ^ 3) +
      1 / (((2 : ℝ) ^ j * a) ^ 4 * k ^ 6))) :
    Summable L ∧ (∑' j, L j) ≤ 4 * D * x / k := by
  have hx : 0 < x := (one_div_pos.mpr hk).trans_le hxk
  have ha := hx.trans_le hxa
  let b := fun j : ℕ => 1 / (((2 : ℝ) ^ j * a) * k ^ 3) +
    1 / (((2 : ℝ) ^ j * a) ^ 4 * k ^ 6)
  have hb := hasSum_empirical_dyadic_terms ha hk
  have hsumBudget : Summable (fun j => D * b j) := (hb.mul_left D).summable
  have hsum : Summable L := Summable.of_nonneg_of_le hL0 hbound hsumBudget
  refine ⟨hsum, ?_⟩
  have hle := hsum.tsum_le_tsum hbound hsumBudget
  have hmul : (∑' j, D * b j) = D * ∑' j, b j := by rw [tsum_mul_left]
  rw [hmul] at hle
  have hrate := mul_le_mul_of_nonneg_left (empirical_dyadic_terms_sum_le hk hxk hxa) hD
  have hfinal := hle.trans hrate
  exact hfinal.trans_eq (by ring)

end ProphetSecretary.Analysis
