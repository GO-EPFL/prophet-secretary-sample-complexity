import ProphetSecretary.Statistics.RankTableOutcomes
import ProphetSecretary.Model.RankExecutionComparison

/-!
# Exact reward and reach mixtures for finite-table learners

The mixture draws its table independently of training and online values.
Both conclusions concern the actual causal learner, rather than a numerical
payoff vector supplied as an interface.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

variable {n k : ℕ}

lemma mixedRankTableLearner_action (G : Finset ℝ) (ν : Measure (RankStrategyTable n k G))
    [IsProbabilityMeasure ν] (y : Reservoir n k) (T : RankStrategyTable n k G)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    (mixedRankTableLearner G ν).policy.action (y,T) p x i =
      (finiteRankTablePolicy G T).action (y,()) p x i :=
  mixedRankTableLearner_decide G ν y T (p.symm i) i (x i) (rankHistory p x (p.symm i))

lemma mixedRankTableLearner_reward (G : Finset ℝ) (ν : Measure (RankStrategyTable n k G))
    [IsProbabilityMeasure ν] (y : Reservoir n k) (T : RankStrategyTable n k G)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) :
    (mixedRankTableLearner G ν).policy.reward (y,T) p x = (finiteRankTablePolicy G T).reward (y,()) p x :=
  (mixedRankTableLearner G ν).policy.reward_eq_of_actions (finiteRankTablePolicy G T) (y,T) (y,()) p x
    (fun i => mixedRankTableLearner_action G ν y T p x i)

lemma mixedRankTableLearner_reaches (G : Finset ℝ) (ν : Measure (RankStrategyTable n k G))
    [IsProbabilityMeasure ν] (y : Reservoir n k) (T : RankStrategyTable n k G)
    (p : Equiv.Perm (Fin n)) (x : Fin n → ℝ) (i : Fin n) :
    (mixedRankTableLearner G ν).policy.Reaches (y,T) p x i ↔ (finiteRankTablePolicy G T).Reaches (y,()) p x i :=
  (mixedRankTableLearner G ν).policy.reaches_iff_of_actions (finiteRankTablePolicy G T) (y,T) (y,()) p x
    (fun j => mixedRankTableLearner_action G ν y T p x j) i

lemma mixedRankTableLearner_expectedReward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (G : Finset ℝ) (ν : Measure (RankStrategyTable n k G)) [IsProbabilityMeasure ν] :
    (mixedRankTableLearner G ν).expectedReward P =
      ∑ T, ν.real {T}*(finiteRankTableLearner G T).expectedReward P := by
  have hMean := mixedRankTableValue_integrable_and_integral P G ν (rankTableReward G)
    (measurable_rankTableReward G) (integrable_rankTableReward P hP G)
  change (∫ ω : MixedRankTableWorld n k G, (mixedRankTableLearner G ν).policy.reward ω.2.2 ω.2.1 ω.1
    ∂mixedRankTableWorldLaw P G ν) = _
  calc
    _ = ∫ ω : MixedRankTableWorld n k G, rankTableReward G ω.2.2.2 (ω.1,(ω.2.1,ω.2.2.1))
        ∂mixedRankTableWorldLaw P G ν := integral_congr_ae (Eventually.of_forall fun ω =>
      mixedRankTableLearner_reward G ν ω.2.2.1 ω.2.2.2 ω.2.1 ω.1)
    _ = ∑ T, ν.real {T}*(∫ a, rankTableReward G T a ∂rankTableInputsLaw P) := hMean.2
    _ = _ := by simp_rw [integral_rankTableReward P G]

lemma mixedRankTableLearner_reachProbability (P : Instance n) (G : Finset ℝ)
    (ν : Measure (RankStrategyTable n k G)) [IsProbabilityMeasure ν] (i : Fin n) :
    (mixedRankTableLearner G ν).reachProbability P i =
      ∑ T, ν.real {T}*(finiteRankTableLearner G T).reachProbability P i := by
  have hMean := mixedRankTableValue_integrable_and_integral P G ν (fun T => rankTableReach G T i)
    (fun T => measurable_rankTableReach G T i) (fun T => integrable_rankTableReach P G T i)
  have hEvent : MeasurableSet {ω : MixedRankTableWorld n k G |
      (mixedRankTableLearner G ν).policy.Reaches ω.2.2 ω.2.1 ω.1 i} :=
    (mixedRankTableLearner G ν).policy.measurableSet_reaches (mixedRankTableLearner G ν).policy_isMeasurable
      (measurable_snd.comp measurable_snd) (measurable_fst.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst) i
  have hInt : (∫ ω : MixedRankTableWorld n k G,
      (if (mixedRankTableLearner G ν).policy.Reaches ω.2.2 ω.2.1 ω.1 i then (1 : ℝ) else 0)
      ∂mixedRankTableWorldLaw P G ν) = (mixedRankTableLearner G ν).reachProbability P i := by
    change (∫ ω : MixedRankTableWorld n k G,
        (if (mixedRankTableLearner G ν).policy.Reaches ω.2.2 ω.2.1 ω.1 i then (1 : ℝ) else 0)
        ∂mixedRankTableWorldLaw P G ν) =
      (mixedRankTableWorldLaw P G ν).real {ω | (mixedRankTableLearner G ν).policy.Reaches ω.2.2 ω.2.1 ω.1 i}
    simpa only [Set.indicator_apply,Set.mem_setOf_eq,smul_eq_mul,mul_one] using
      integral_indicator_const (μ := mixedRankTableWorldLaw P G ν) (1 : ℝ) hEvent
  rw [← hInt]
  calc
    _ = ∫ ω : MixedRankTableWorld n k G, rankTableReach G ω.2.2.2 i (ω.1,(ω.2.1,ω.2.2.1))
        ∂mixedRankTableWorldLaw P G ν := by
      apply integral_congr_ae
      exact Eventually.of_forall fun ω => by
        rcases ω with ⟨x,p,y,T⟩
        change (if (mixedRankTableLearner G ν).policy.Reaches (y,T) p x i then (1 : ℝ) else 0) =
          (if (finiteRankTablePolicy G T).Reaches (y,()) p x i then (1 : ℝ) else 0)
        rw [mixedRankTableLearner_reaches G ν y T p x i]
    _ = ∑ T, ν.real {T}*(∫ a, rankTableReach G T i a ∂rankTableInputsLaw P) := hMean.2
    _ = _ := by simp_rw [integral_rankTableReach P G]

end ProphetSecretary.Statistics
