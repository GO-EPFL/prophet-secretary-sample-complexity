import ProphetSecretary.Statistics.FiniteRankBayesMinimax
import ProphetSecretary.Model.RankValueActions

/-!
# Finite Bayes-to-minimax conversion in the paper's clock model

Every-prior clock responses are first represented causally in ranks; an
actual universal finite-table mixture is then transported back to clocks.
The conversion preserves reward, each reach probability, exact sample counts,
and the all-outcome cap/zero decisions. The statistical response hypothesis
is quantified before the universal learner.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Model
variable {n k : ℕ}

lemma Learner.clockToRank_targetGamePayoff (L : Learner n k) (P : Instance n)
    (J : Option (Fin n)) (C : ℝ) : L.clockToRank.targetGamePayoff P J C=L.targetGamePayoff P J C := by
  cases J <;> simp only [Learner.targetGamePayoff,RankLearner.targetGamePayoff,
    L.clockToRank_expectedReward,L.clockToRank_reachProbability]

end ProphetSecretary.Model

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n k : ℕ} {Θ : Type*} [Fintype Θ]

theorem finite_clock_learner_of_bayes_responses (G : Finset ℝ) (P : Θ → Instance n)
    (hP : ∀ θ, Integrable Instance.maximum (P θ).valuesLaw)
    (hG : ∀ θ i, ∀ᵐ x ∂(P θ).law i, x∈G) (J : Θ → Option (Fin n)) (C t : ℝ)
    (hBayes : ∀ p∈stdSimplex ℝ Θ, ∃ L : Learner n k,
      (∀ y r s i H, L.policy.decide (y,r) s i 1 H = true) ∧
      (∀ y r s i H, L.policy.decide (y,r) s i 0 H = false) ∧
      t ≤ ∑ θ, p θ*L.targetGamePayoff (P θ) (J θ) C) :
    ∃ L : Learner n k,
      (∀ y r s i H, L.policy.decide (y,r) s i 1 H = true) ∧
      (∀ y r s i H, L.policy.decide (y,r) s i 0 H = false) ∧
      (∀ (y : Reservoir n k) (r : L.Seed) (i : Fin n), requests (trainingTranscript L.request r y) i = k) ∧
      ∀ θ, t ≤ L.targetGamePayoff (P θ) (J θ) C := by
  have hRank : ∀ p∈stdSimplex ℝ Θ, ∃ L : RankLearner n k,
      (∀ y r q i H, L.policy.decide (y,r) q i 1 H=true) ∧
      (∀ y r q i H, L.policy.decide (y,r) q i 0 H=false) ∧
      t ≤ ∑ θ, p θ*L.targetGamePayoff (P θ) (J θ) C := by
    intro p hp
    obtain ⟨L,hCap,hZero,hMean⟩ := hBayes p hp
    refine ⟨L.clockToRank,?_,?_,?_⟩
    · intro y r q i H
      exact L.clockToRank_fixedAction 1 true hCap y r q i H
    · intro y r q i H
      exact L.clockToRank_fixedAction 0 false hZero y r q i H
    · simpa only [L.clockToRank_targetGamePayoff] using hMean
  obtain ⟨L,hCap,hZero,hBudget,hUniversal⟩ := finite_rank_learner_of_bayes_responses G P hP hG J C t hRank
  refine ⟨L.rankToClock,?_,?_,?_,?_⟩
  · intro y r s i H
    exact L.rankToClock_fixedAction 1 true hCap y r s i H
  · intro y r s i H
    exact L.rankToClock_fixedAction 0 false hZero y r s i H
  · intro y r i
    exact hBudget y r i
  · intro θ
    rw [L.rankToClock_targetGamePayoff]
    exact hUniversal θ

end ProphetSecretary.Statistics
