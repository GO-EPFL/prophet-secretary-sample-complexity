import ProphetSecretary.Statistics.MixedWeightedCriticalMoments
import ProphetSecretary.Statistics.GridCriticalPrefixes

/-!
# One actual grid entrance with mixed-law error

The first true-critical grid event is observable in elapsed clocks. Its actual
remaining-size multiplier therefore applies to the proved mixed conditional
moments without any assumption of size/error independence.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

/-- A single grid entrance has the source's weighted localized moment bound. -/
theorem Instance.mixedGridEntrance_weighted_moment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (j : ℕ) (ht0 : 0 ≤ τ j) (ht1 : τ j < 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    (∫ q, P.gridEntranceSizeMultiplier τ hi a j q * P.mixedStateFutureError known k lo hi (τ j) q ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p * ∫ q, P.gridEntranceSizeMultiplier τ hi a j q
        ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n) := by
  apply P.weighted_critical_mixedStateFutureError_moment known hbound hlo hlohi hhi ht0 ht1 hp
    (P.gridEntranceSizeMultiplier τ hi a j) (P.stronglyMeasurable_gridEntranceSizeMultiplier τ hτ hi a j)
    (by linarith [P.totalFirstMoment_nonnegative] : 0 ≤ P.totalFirstMoment+1)
    (Eventually.of_forall fun q => P.gridEntranceSizeMultiplier_mem τ hi a j ht0 ht1.le q)
  intro q hne
  by_cases he : P.firstCriticalGridEvent τ hi a j q.2
  · exact he.1
  · exact False.elim (hne (if_neg he))

end ProphetSecretary.Model
