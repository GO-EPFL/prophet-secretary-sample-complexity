import ProphetSecretary.Statistics.RankTargetPayoff
import ProphetSecretary.Statistics.FiniteRankBayesMinimax
import ProphetSecretary.Analysis.FiniteRateProgram

/-!
# An actual learner from the finite competitive ratio program

The program chooses its table distribution and rate before training and
before nature's hidden action. Its constraints are the actual expected reward
and reach of the pure learners. The statistical Bayes premise is needed only
for the quantitative lower bound on the maximizer's rate.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Analysis

variable {n k : ℕ} {Θ : Type*}

noncomputable def rankTablePayoffMatrix (G : Finset ℝ) (P : Θ → Instance n) (J : Θ → Option (Fin n))
    (T : RankStrategyTable n k G) (θ : Θ) : ℝ := (finiteRankTableLearner G T).targetPayoff (P θ) (J θ)

noncomputable def rankTableBenchmarks (P : Θ → Instance n) (J : Θ → Option (Fin n)) (θ : Θ) : ℝ :=
  targetBenchmark (P θ) (J θ)

lemma rankTablePayoffMatrix_nonnegative (G : Finset ℝ) (P : Θ → Instance n) (J : Θ → Option (Fin n))
    (T : RankStrategyTable n k G) (θ : Θ) : 0 ≤ rankTablePayoffMatrix G P J T θ :=
  (finiteRankTableLearner G T).targetPayoff_nonnegative (P θ) (J θ)

noncomputable def rankTableRateOptimizer (G : Finset ℝ) (P : Θ → Instance n) (J : Θ → Option (Fin n)) :
    (RankStrategyTable n k G → ℝ) × ℝ :=
  (exists_finite_rate_maximizer (rankTablePayoffMatrix G P J) (rankTableBenchmarks P J)
    (rankTablePayoffMatrix_nonnegative G P J)).choose

lemma rankTableRateOptimizer_spec (G : Finset ℝ) (P : Θ → Instance n) (J : Θ → Option (Fin n)) :
    rankTableRateOptimizer (k := k) G P J∈finiteRateFeasible (rankTablePayoffMatrix G P J) (rankTableBenchmarks P J) ∧
    ∀ w∈finiteRateFeasible (rankTablePayoffMatrix (k := k) G P J) (rankTableBenchmarks P J),
      w.2 ≤ (rankTableRateOptimizer (k := k) G P J).2 :=
  (exists_finite_rate_maximizer (rankTablePayoffMatrix G P J) (rankTableBenchmarks P J)
    (rankTablePayoffMatrix_nonnegative G P J)).choose_spec

noncomputable def rankTableRateLaw (G : Finset ℝ) (P : Θ → Instance n) (J : Θ → Option (Fin n)) :
    Measure (RankStrategyTable n k G) :=
  finiteSimplexLaw (rankTableRateOptimizer G P J).1 (rankTableRateOptimizer_spec G P J).1.1

instance rankTableRateLaw_probability (G : Finset ℝ) (P : Θ → Instance n) (J : Θ → Option (Fin n)) :
    IsProbabilityMeasure (rankTableRateLaw (k := k) G P J) := by unfold rankTableRateLaw;infer_instance

noncomputable def rankTableRateLearner (G : Finset ℝ) (P : Θ → Instance n) (J : Θ → Option (Fin n)) : RankLearner n k :=
  mixedRankTableLearner G (rankTableRateLaw G P J)

lemma rankTableRateLearner_requests_eq (G : Finset ℝ) (P : Θ → Instance n) (J : Θ → Option (Fin n))
    (y : Reservoir n k) (r : RankStrategyTable n k G) (i : Fin n) :
    requests (trainingTranscript (rankTableRateLearner G P J).request r y) i = k :=
  mixedRankTableLearner_requests_eq G _ y r i

lemma rankTableRateLearner_constraints (G : Finset ℝ) (P : Θ → Instance n) (J : Θ → Option (Fin n))
    (hP : ∀ θ, Integrable Instance.maximum (P θ).valuesLaw) (θ : Θ) :
    (rankTableRateOptimizer (k := k) G P J).2*targetBenchmark (P θ) (J θ) ≤
      (rankTableRateLearner (k := k) G P J).targetPayoff (P θ) (J θ) := by
  have hMix := mixedRankTableLearner_targetPayoff (P θ) (hP θ) G (rankTableRateLaw (k := k) G P J) (J θ)
  change _ ≤ (mixedRankTableLearner G (rankTableRateLaw (k := k) G P J)).targetPayoff (P θ) (J θ)
  rw [hMix]
  change _ ≤ ∑ T, (finiteSimplexLaw (rankTableRateOptimizer (k := k) G P J).1
    (rankTableRateOptimizer_spec (k := k) G P J).1.1).real {T}*
    (finiteRankTableLearner G T).targetPayoff (P θ) (J θ)
  simp_rw [finiteSimplexLaw_real_singleton]
  exact (rankTableRateOptimizer_spec (k := k) G P J).1.2.2 θ

/-- The rate bound is independent of the cardinality of the strategy and nature
sets. The every-prior response premise remains explicit. -/
theorem rankTableRateOptimizer_ge_of_bayes [Fintype Θ] (G : Finset ℝ) (P : Θ → Instance n)
    (J : Θ → Option (Fin n)) (hP : ∀ θ, Integrable Instance.maximum (P θ).valuesLaw)
    (hG : ∀ θ i, ∀ᵐ x ∂(P θ).law i, x∈G) {C κ β : ℝ}
    (hC : C ≤ 1) (hκ : 0 ≤ κ) (hβ : 0 < β) (hBench : ∀ θ, β ≤ targetBenchmark (P θ) (J θ))
    (hBayes : ∀ p∈stdSimplex ℝ Θ, ∃ L : RankLearner n k,
      (∀ y r q i H, L.policy.decide (y,r) q i 1 H=true) ∧
      (∀ y r q i H, L.policy.decide (y,r) q i 0 H=false) ∧
      -κ ≤ ∑ θ, p θ*L.targetGamePayoff (P θ) (J θ) C) :
    C-κ/β ≤ (rankTableRateOptimizer (k := k) G P J).2 := by
  obtain ⟨p,hp,hUniversal⟩ := finite_rank_mixture_of_bayes_responses G P hP hG J C (-κ) hBayes
  have hDeficit (θ : Θ) : C*rankTableBenchmarks P J θ-κ ≤ ∑ T, p T*rankTablePayoffMatrix G P J T θ := by
    have h := hUniversal θ
    simp only [RankLearner.targetGamePayoff_eq] at h
    simp_rw [mul_sub] at h
    rw [Finset.sum_sub_distrib,← Finset.sum_mul,hp.2,one_mul] at h
    dsimp only [rankTableBenchmarks,rankTablePayoffMatrix]
    linarith only [h]
  have hCandidate := feasible_rate_of_deficit (rankTablePayoffMatrix G P J) (rankTableBenchmarks P J)
    (rankTablePayoffMatrix_nonnegative G P J) p hp hC hκ hβ hBench hDeficit
  exact (le_max_right _ _).trans ((rankTableRateOptimizer_spec (k := k) G P J).2 _ hCandidate)

end ProphetSecretary.Statistics
