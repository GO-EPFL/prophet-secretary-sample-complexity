import ProphetSecretary.Statistics.MixedGridEntranceMoments
import ProphetSecretary.Statistics.GridEntranceVariables

/-!
# Concrete mixed finite-grid error and true entrance size

The first true-critical event activates at most one mixed state error. Its
product with the original true remaining-size variable equals the proved
weighted sum. A missing entrance contributes zero, and no grid-cardinality
factor is introduced.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

noncomputable def Instance.mixedGridEntranceError (P : Instance n) (known : Finset (Fin n)) (k : ℕ) [NeZero k]
    (τ : ℕ → ℝ) (lo hi a : ℝ) (N : ℕ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) : ℝ :=
  ∑ j ∈ Finset.range N, if P.firstCriticalGridEvent τ hi a j q.2 then P.mixedStateFutureError known k lo hi (τ j) q else 0

lemma Instance.mixedGridEntrance_size_error_identity (P : Instance n) (known : Finset (Fin n)) (τ : ℕ → ℝ) (lo hi a : ℝ)
    (N p : ℕ) (q : (((Fin n × Fin k) → ℝ) × (Fin n → ℝ))) :
    P.gridEntranceSize k τ hi a N q * P.mixedGridEntranceError known k τ lo hi a N q ^ p =
      ∑ j ∈ Finset.range N, P.gridEntranceSizeMultiplier τ hi a j q * P.mixedStateFutureError known k lo hi (τ j) q ^ p := by
  exact ProphetSecretary.Statistics.product_sums_one_active (Finset.range N)
    (fun j => P.firstCriticalGridEvent τ hi a j q.2)
    (fun i _ j _ hEi hEj => P.firstCriticalGridEvent_unique τ hi a q.2 hEi hEj)
    (fun j => P.remainingSize (τ j) q.2) (fun j => P.mixedStateFutureError known k lo hi (τ j) q) p

/-- A genuine random finite-grid entrance has the desired weighted moments. -/
theorem Instance.mixedGridEntrance_weightedError_moment (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {lo hi a : ℝ}
    (hlo : 0 ≤ lo) (hlohi : lo ≤ hi) (hhi : 0 < hi) (ha : 0 ≤ a)
    (τ : ℕ → ℝ) (hτ : Monotone τ) (N : ℕ) (hTimes : ∀ j < N, τ j ∈ Ico (0 : ℝ) 1)
    {p : ℕ} (hp : p=2 ∨ p=6) :
    Integrable (fun q => P.gridEntranceSize k τ hi a N q * P.mixedGridEntranceError known k τ lo hi a N q ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ∧
    (∫ q, P.gridEntranceSize k τ hi a N q * P.mixedGridEntranceError known k τ lo hi a N q ^ p
      ∂(P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) ≤
      empiricalRestartMomentBound k lo hi a p * (a*(1+P.totalFirstMoment)/hi) := by
  have hI : Integrable (fun q => ∑ j ∈ Finset.range N,
      P.gridEntranceSizeMultiplier τ hi a j q * P.mixedStateFutureError known k lo hi (τ j) q ^ p)
      ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n)) :=
    integrable_finsetSum _ fun j hj => P.integrable_mixedGridEntrance_weightedError (k := k) known hbound τ hτ lo hi a j
      (hTimes j (Finset.mem_range.mp hj)).1 (hTimes j (Finset.mem_range.mp hj)).2 p
  have heq : (fun q => P.gridEntranceSize k τ hi a N q * P.mixedGridEntranceError known k τ lo hi a N q ^ p) =
      (fun q => ∑ j ∈ Finset.range N, P.gridEntranceSizeMultiplier τ hi a j q * P.mixedStateFutureError known k lo hi (τ j) q ^ p) :=
    funext fun q => P.mixedGridEntrance_size_error_identity known τ lo hi a N p q
  rw [heq]
  exact ⟨hI,P.integral_mixedGridEntrance_weightedError_sum_le known hbound hlo hlohi hhi ha τ hτ N hTimes hp⟩

end ProphetSecretary.Model
