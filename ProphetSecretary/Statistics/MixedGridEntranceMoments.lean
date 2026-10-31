import ProphetSecretary.Statistics.MixedGridCriticalMoments
import ProphetSecretary.Statistics.GridEntranceMoments

/-!
# Actual weighted mixed moments at finite-grid entrances

Only the first true-critical grid event contributes. The conditional mixed
moment and true entrance-size estimate combine without a factor depending on
the number of grid times or identities.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

lemma Instance.integrable_mixedGridEntrance_weightedError (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (τ : ℕ → ℝ) (hτ : Monotone τ)
    (lo hi a : ℝ) (j : ℕ) (ht0 : 0 ≤ τ j) (ht1 : τ j < 1) (p : ℕ) :
    Integrable (fun q => P.gridEntranceSizeMultiplier (k := k) τ hi a j q * P.mixedStateFutureError known k lo hi (τ j) q ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) := by
  have hHm := (P.stronglyMeasurable_gridEntranceSizeMultiplier (k := k) τ hτ hi a j).mono
    (ProphetSecretary.Probability.observedClockSigma_le (τ j))
  have hm : AEStronglyMeasurable (fun q => P.gridEntranceSizeMultiplier (k := k) τ hi a j q *
      P.mixedStateFutureError known k lo hi (τ j) q ^ p) ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) :=
    hHm.aestronglyMeasurable.mul ((P.measurable_mixedStateFutureError known lo hi (τ j)).pow_const p).aestronglyMeasurable
  apply Integrable.of_bound hm ((P.totalFirstMoment+1)*(2*(n : ℝ))^p)
  filter_upwards [P.mixedStateFutureError_bounded (k := k) known hbound lo hi ht0 ht1] with q hq
  have hH := P.gridEntranceSizeMultiplier_mem (k := k) τ hi a j ht0 ht1.le q
  have hE := P.mixedStateFutureError_nonnegative (k := k) known lo hi (τ j) q
  change ‖P.gridEntranceSizeMultiplier τ hi a j q * P.mixedStateFutureError known k lo hi (τ j) q ^ p‖ ≤ _
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hH.1 (pow_nonneg hE p))]
  exact mul_le_mul hH.2 (pow_le_pow_left₀ hE hq p) (pow_nonneg hE p)
    (by linarith [P.totalFirstMoment_nonnegative])

/-- Discrete-grid weighted moments underlying the entrance argument, with no
factor depending on the grid cardinality. -/
theorem Instance.integral_mixedGridEntrance_weightedError_sum_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ha : 0 ≤ a)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (N : ℕ) (hTimes : ∀ j < N, τ j ∈ Ico (0 : ℝ) 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    (∫ q, ∑ j ∈ Finset.range N, P.gridEntranceSizeMultiplier (k := k) τ hi a j q * P.mixedStateFutureError known k lo hi (τ j) q ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p * (a*(1+P.totalFirstMoment)/hi) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hI (j : ℕ) (hj : j ∈ Finset.range N) := P.integrable_mixedGridEntrance_weightedError (k := k) known
    hbound τ hτ lo hi a j (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2 p
  rw [integral_finsetSum _ hI]
  have hsum := Finset.sum_le_sum (s := Finset.range N) (fun j hj =>
    P.mixedGridEntrance_weighted_moment (k := k) (a := a) known hbound hlo hlohi hhi τ hτ j
      (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2 hp)
  apply hsum.trans
  rw [← Finset.mul_sum]
  have hH (j : ℕ) (hj : j ∈ Finset.range N) := P.gridEntranceSizeMultiplier_integrable (k := k) τ hτ hi a j
    (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2.le
  rw [← integral_finsetSum _ hH]
  exact mul_le_mul_of_nonneg_left
    (P.integral_gridEntranceSize_sum_le (k := k) hP τ hτ hhi ha N
      (fun j hj => ⟨(hTimes j hj).1,(hTimes j hj).2.le⟩))
    (empiricalRestartMomentBound_nonnegative k hhi ha p)

end ProphetSecretary.Model
