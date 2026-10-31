import ProphetSecretary.Model.FiniteAlphabetLearner
import ProphetSecretary.Model.FiniteAlphabetRounding

/-!
# Reward and reach guarantees transferred from rounded probabilities

For k training samples per marginal, the full experiment changes with
probability at most (k+1)d. The prophet benchmark loses at most d, giving
the (k+2)d reward deficit in the proof of `upbayes:theorem`.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n k : ℕ} {Θ : Type*} [Fintype Θ] [DecidableEq Θ]
  [MeasurableSpace Θ] [MeasurableSingletonClass Θ]

theorem rankLearner_rounding_guarantee_transfer (L : RankLearner n k) (v : Θ → ℝ)
    (hv : ∀ a, v a∈Icc (0 : ℝ) 1) (p : Fin n → Θ → ℝ) (hp : ∀ i, p i∈stdSimplex ℝ Θ)
    (N : ℕ) (hN : 0<N) (z : Θ) {γ : ℝ} (hγ : γ∈Icc (0 : ℝ) 1)
    (hReward : γ*(finiteAlphabetInstance v (fun a => (hv a).1)
      (fun i => roundedProbability (p i) N z) (fun i => roundedProbability_simplex (p i) (hp i) hN z)).expectedMaximum ≤
      L.expectedReward (finiteAlphabetInstance v (fun a => (hv a).1)
        (fun i => roundedProbability (p i) N z) (fun i => roundedProbability_simplex (p i) (hp i) hN z)))
    (hReach : ∀ i, γ≤L.reachProbability (finiteAlphabetInstance v (fun a => (hv a).1)
      (fun i => roundedProbability (p i) N z) (fun i => roundedProbability_simplex (p i) (hp i) hN z)) i) :
    γ*(finiteAlphabetInstance v (fun a => (hv a).1) p hp).expectedMaximum-
        ((k : ℝ)+2)*(∑ i, roundingLoss (p i) N z) ≤
      L.expectedReward (finiteAlphabetInstance v (fun a => (hv a).1) p hp) ∧
    ∀ i, γ-((k : ℝ)+1)*(∑ j, roundingLoss (p j) N z) ≤
      L.reachProbability (finiteAlphabetInstance v (fun a => (hv a).1) p hp) i := by
  have hd : 0≤∑ i, roundingLoss (p i) N z :=
    Finset.sum_nonneg (fun i _ => roundingLoss_nonnegative (p i) (hp i) hN z)
  have hM := (abs_le.mp (finiteAlphabetInstance_rounding_maximum_error v hv p hp N hN z)).2
  have hγM := mul_le_mul_of_nonneg_left hM hγ.1
  have hγd : γ*(∑ i, roundingLoss (p i) N z)≤∑ i, roundingLoss (p i) N z :=
    mul_le_of_le_one_left hd hγ.2
  constructor
  · have hR := (abs_le.mp (L.rounding_reward_error v hv p hp N hN z)).1
    nlinarith only [hReward,hR,hγM,hγd]
  · intro i
    have hQ := (abs_le.mp (L.rounding_reach_error v (fun a => (hv a).1) p hp N hN z i)).1
    linarith only [hReach i,hQ]

end ProphetSecretary.Statistics
