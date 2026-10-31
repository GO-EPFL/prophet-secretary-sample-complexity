import ProphetSecretary.Limiting.HybridMarkovThreshold
import ProphetSecretary.Model.ThresholdExecutionContinuity

/-!
# Regular-world continuity for count-hidden hybrid Markov threshold branches

At each analytically fixed anonymous count, the actual finite adapter is the
proved finite threshold rule. Its continuity follows from the count-hidden
callback's time continuity. No anonymous count is disclosed to the executed
policy, and no AE regularity or canonical hybrid optimizer is assumed here.
-/
open Set Filter
open scoped Topology Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ} {Seed : Type*}

lemma finiteHybridThreshold_continuous
    (θ : Seed → Finset (Fin n) → ℝ → Option (Fin n) → ℝ) (N : ℕ) (r : Seed)
    (hθ : ∀ A i, Continuous (fun t => θ r A t i)) (A : Finset (Fin (n+N))) (k : Fin (n+N)) :
    Continuous (fun t => finiteHybridThreshold θ N r A t k) := by
  induction k using Fin.addCases with
  | left i => simpa only [finiteHybridThreshold,Fin.addCases_left] using hθ (retainedUnseen A) (some i)
  | right j => simpa only [finiteHybridThreshold,Fin.addCases_right] using hθ (retainedUnseen A) none

theorem hybridThresholdRule_finite_outcomes_continuousAt
    (θ : Seed → Finset (Fin n) → ℝ → Option (Fin n) → ℝ) (N : ℕ) (r : Seed)
    (hθ : ∀ A i, Continuous (fun t => θ r A t i)) (D : Finset (Fin (n+N)))
    (x u : Fin (n+N) → ℝ) (hu : Function.Injective u) (hterm : ∀ i, u i ≠ 1)
    (htie : ∀ i, x i ≠ finiteHybridThreshold θ N r (Model.unseen (Model.history D x u (u i))) (u i) i) :
    ContinuousAt (fun z : (Fin (n+N) → ℝ) × (Fin (n+N) → ℝ) =>
      ((hybridThresholdRule θ).asFinitePolicy N).reward r D z.1 z.2) (x,u) ∧
    ContinuousAt (fun z : (Fin (n+N) → ℝ) × (Fin (n+N) → ℝ) =>
      ((hybridThresholdRule θ).asFinitePolicy N).stoppingTime r D z.1 z.2) (x,u) := by
  rw [hybridThresholdRule_asFinitePolicy]
  exact Model.thresholdPolicy.outcomes_continuousAt (finiteHybridThreshold θ N) r
    (finiteHybridThreshold_continuous θ N r hθ) D x u hu hterm htie

end ProphetSecretary.Limiting
