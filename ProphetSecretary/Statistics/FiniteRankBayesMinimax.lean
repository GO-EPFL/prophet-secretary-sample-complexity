import ProphetSecretary.Statistics.RankTargetGame
import ProphetSecretary.Analysis.FiniteMinimax

/-!
# Finite Bayes-to-minimax conversion for actual rank learners

The hypothesis supplies a cap-accepting, zero-rejecting response to every
prior on a fixed finite family. Measurable finite strategy encoding and the
checked finite minimax theorem produce one actual learner for the entire
family, with its hard budget valid on every outcome. This isolates the
minimax conversion in the proof of `upbayes:theorem`.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis

variable {n k : ℕ} {Θ : Type*} [Fintype Θ]

theorem finite_rank_learner_of_bayes_responses (G : Finset ℝ) (P : Θ → Instance n)
    (hP : ∀ θ, Integrable Instance.maximum (P θ).valuesLaw)
    (hG : ∀ θ i, ∀ᵐ x ∂(P θ).law i, x∈G) (J : Θ → Option (Fin n)) (C t : ℝ)
    (hBayes : ∀ p∈stdSimplex ℝ Θ, ∃ L : RankLearner n k,
      (∀ y r q i H, L.policy.decide (y,r) q i 1 H = true) ∧
      (∀ y r q i H, L.policy.decide (y,r) q i 0 H = false) ∧
      t ≤ ∑ θ, p θ*L.targetGamePayoff (P θ) (J θ) C) :
    ∃ L : RankLearner n k,
      (∀ y r q i H, L.policy.decide (y,r) q i 1 H = true) ∧
      (∀ y r q i H, L.policy.decide (y,r) q i 0 H = false) ∧
      (∀ (y : Reservoir n k) (r : L.Seed) (i : Fin n), requests (trainingTranscript L.request r y) i = k) ∧
      ∀ θ, t ≤ L.targetGamePayoff (P θ) (J θ) C := by
  let u := fun (T : RankStrategyTable n k G) (θ : Θ) =>
    (finiteRankTableLearner G T).targetGamePayoff (P θ) (J θ) C
  have hResponse : ∀ p∈stdSimplex ℝ Θ,
      ∃ q∈stdSimplex ℝ (RankStrategyTable n k G), t ≤ finiteGamePayoff u p q := by
    intro p hp
    obtain ⟨L,hCap,hZero,hMean⟩ := hBayes p hp
    let ν := rankLearnerTableLaw L G
    let q := fun T : RankStrategyTable n k G => ν.real {T}
    have hq : q∈stdSimplex ℝ (RankStrategyTable n k G) := finiteProbability_singletons_simplex ν
    have hEach (θ : Θ) : (∑ T, u T θ*q T) = L.targetGamePayoff (P θ) (J θ) C := by
      calc
        _ = ∑ T, ν.real {T}*(finiteRankTableLearner G T).targetGamePayoff (P θ) (J θ) C := by
          apply Finset.sum_congr rfl
          intro T _
          exact mul_comm _ _
        _ = (rankLearnerTableMixture L G).targetGamePayoff (P θ) (J θ) C :=
          (mixedRankTableLearner_targetGamePayoff (P θ) (hP θ) G ν (J θ) C).symm
        _ = _ := rankLearnerTableMixture_targetGamePayoff L G hCap hZero (P θ) (hP θ) (hG θ) (J θ) C
    have hEq : finiteGamePayoff u p q = ∑ θ, p θ*L.targetGamePayoff (P θ) (J θ) C := by
      unfold finiteGamePayoff
      apply Finset.sum_congr rfl
      intro θ _
      rw [hEach θ]
      ring
    exact ⟨q,hq,hMean.trans_eq hEq.symm⟩
  obtain ⟨q,hq,hUniversal⟩ := finite_minimax_response u t hResponse
  let ν := finiteSimplexLaw q hq
  refine ⟨mixedRankTableLearner G ν,?_,?_,?_,?_⟩
  · intro y r a i H
    exact (mixedRankTableLearner_decide G ν y r a i 1 H).trans
      (finiteRankTablePolicy_accepts_cap G r y () a i H)
  · intro y r a i H
    exact (mixedRankTableLearner_decide G ν y r a i 0 H).trans
      (finiteRankTablePolicy_rejects_zero G r y () a i H)
  · intro y r i
    exact mixedRankTableLearner_requests_eq G ν y r i
  · intro θ
    have hEq : (mixedRankTableLearner G ν).targetGamePayoff (P θ) (J θ) C = ∑ T, u T θ*q T := by
      rw [mixedRankTableLearner_targetGamePayoff (P θ) (hP θ) G ν (J θ) C]
      change (∑ T, (finiteSimplexLaw q hq).real {T}*
        (finiteRankTableLearner G T).targetGamePayoff (P θ) (J θ) C) = _
      simp_rw [finiteSimplexLaw_real_singleton q hq]
      apply Finset.sum_congr rfl
      intro T _
      exact mul_comm _ _
    exact (hUniversal θ).trans_eq hEq.symm

/-- A numeric mixture witness in the same finite strategy alphabet, for use in
the constrained competitive ratio program. -/
theorem finite_rank_mixture_of_bayes_responses (G : Finset ℝ) (P : Θ → Instance n)
    (hP : ∀ θ, Integrable Instance.maximum (P θ).valuesLaw)
    (hG : ∀ θ i, ∀ᵐ x ∂(P θ).law i, x∈G) (J : Θ → Option (Fin n)) (C t : ℝ)
    (hBayes : ∀ p∈stdSimplex ℝ Θ, ∃ L : RankLearner n k,
      (∀ y r q i H, L.policy.decide (y,r) q i 1 H = true) ∧
      (∀ y r q i H, L.policy.decide (y,r) q i 0 H = false) ∧
      t ≤ ∑ θ, p θ*L.targetGamePayoff (P θ) (J θ) C) :
    ∃ q∈stdSimplex ℝ (RankStrategyTable n k G), ∀ θ,
      t ≤ ∑ T, q T*(finiteRankTableLearner G T).targetGamePayoff (P θ) (J θ) C := by
  obtain ⟨L,hCap,hZero,_hBudget,hUniversal⟩ := finite_rank_learner_of_bayes_responses G P hP hG J C t hBayes
  let ν := rankLearnerTableLaw L G
  refine ⟨(fun T => ν.real {T}),finiteProbability_singletons_simplex ν,?_⟩
  intro θ
  have hEq : (∑ T, ν.real {T}*(finiteRankTableLearner G T).targetGamePayoff (P θ) (J θ) C) =
      L.targetGamePayoff (P θ) (J θ) C :=
    (mixedRankTableLearner_targetGamePayoff (P θ) (hP θ) G ν (J θ) C).symm.trans
      (rankLearnerTableMixture_targetGamePayoff L G hCap hZero (P θ) (hP θ) (hG θ) (J θ) C)
  exact (hUniversal θ).trans_eq hEq.symm

end ProphetSecretary.Statistics
