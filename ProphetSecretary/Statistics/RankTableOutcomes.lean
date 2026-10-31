import ProphetSecretary.Statistics.MixedRankTableLearner
import Mathlib.Probability.HasLaw

/-!
# Reward and reach of an actual pure table learner

The independent Unit seed is immaterial. Removing it gives a common product
input space for all pure tables. Measurability and integrability are proved
for the actual reward and reach indicator before identifying their means.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Statistics
open ProphetSecretary.Model

variable {n k : ℕ}

noncomputable def rankTableReward (G : Finset ℝ) (T : RankStrategyTable n k G) (ω : RankTableInputs n k) : ℝ :=
  (finiteRankTablePolicy G T).reward (ω.2.2,()) ω.2.1 ω.1

noncomputable def rankTableReach (G : Finset ℝ) (T : RankStrategyTable n k G) (i : Fin n)
    (ω : RankTableInputs n k) : ℝ :=
  if (finiteRankTablePolicy G T).Reaches (ω.2.2,()) ω.2.1 ω.1 i then 1 else 0

lemma measurable_rankTableReward (G : Finset ℝ) (T : RankStrategyTable n k G) : Measurable (rankTableReward G T) :=
  (finiteRankTablePolicy G T).measurable_reward (finiteRankTablePolicy_measurable G T)
    ((measurable_snd.comp measurable_snd).prodMk measurable_const)
    (measurable_fst.comp measurable_snd) (fun i => (measurable_pi_apply i).comp measurable_fst)

lemma measurableSet_rankTableReaches (G : Finset ℝ) (T : RankStrategyTable n k G) (i : Fin n) :
    MeasurableSet {ω : RankTableInputs n k | (finiteRankTablePolicy G T).Reaches (ω.2.2,()) ω.2.1 ω.1 i} :=
  (finiteRankTablePolicy G T).measurableSet_reaches (finiteRankTablePolicy_measurable G T)
    ((measurable_snd.comp measurable_snd).prodMk measurable_const)
    (measurable_fst.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst) i

lemma measurable_rankTableReach (G : Finset ℝ) (T : RankStrategyTable n k G) (i : Fin n) :
    Measurable (rankTableReach G T i) :=
  Measurable.ite (measurableSet_rankTableReaches G T i) measurable_const measurable_const

lemma integrable_rankTableReward (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw)
    (G : Finset ℝ) (T : RankStrategyTable n k G) : Integrable (rankTableReward G T) (rankTableInputsLaw P) := by
  have hp : MeasurePreserving (fun ω : RankTableInputs n k => ω.1) (rankTableInputsLaw P) P.valuesLaw :=
    measurePreserving_fst
  apply (hp.integrable_comp_of_integrable hP).mono' (measurable_rankTableReward G T).aestronglyMeasurable
  filter_upwards [hp.quasiMeasurePreserving.ae P.ae_nonnegative] with ω hω
  change ‖(finiteRankTablePolicy G T).reward (ω.2.2,()) ω.2.1 ω.1‖ ≤ Instance.maximum ω.1
  rw [Real.norm_eq_abs,abs_of_nonneg ((finiteRankTablePolicy G T).reward_nonnegative _ _ _ hω)]
  exact (finiteRankTablePolicy G T).reward_le_maximum _ _ _

lemma integrable_rankTableReach (P : Instance n) (G : Finset ℝ) (T : RankStrategyTable n k G) (i : Fin n) :
    Integrable (rankTableReach G T i) (rankTableInputsLaw P) := by
  apply Integrable.of_bound (measurable_rankTableReach G T i).aestronglyMeasurable 1
  exact Eventually.of_forall fun ω => by unfold rankTableReach; split_ifs <;> norm_num

lemma rankUnitInputs_measurePreserving (P : Instance n) :
    MeasurePreserving (fun ω : (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n k × Unit)) =>
      (ω.1,(ω.2.1,ω.2.2.1)))
      (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ((P.reservoirLaw k).prod (Measure.dirac ()))))
      (rankTableInputsLaw P) :=
  (MeasurePreserving.id P.valuesLaw).prod ((MeasurePreserving.id (Instance.uniformPermutationLaw n)).prod
    (measurePreserving_fst (μ := P.reservoirLaw k) (ν := Measure.dirac ())))

lemma integral_rankTableReward (P : Instance n) (G : Finset ℝ) (T : RankStrategyTable n k G) :
    (∫ ω, rankTableReward G T ω ∂rankTableInputsLaw P) = (finiteRankTableLearner G T).expectedReward P := by
  change (∫ ω, rankTableReward G T ω ∂rankTableInputsLaw P) =
    ∫ ω : (Fin n → ℝ) × (Equiv.Perm (Fin n) × (Reservoir n k × Unit)),
      (finiteRankTableLearner G T).policy.reward ω.2.2 ω.2.1 ω.1
      ∂P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ((P.reservoirLaw k).prod (Measure.dirac ())))
  rw [finiteRankTableLearner_policy]
  exact ((rankUnitInputs_measurePreserving (k := k) P).hasLaw.integral_comp
    (measurable_rankTableReward G T).aestronglyMeasurable).symm

lemma integral_rankTableReach (P : Instance n) (G : Finset ℝ) (T : RankStrategyTable n k G) (i : Fin n) :
    (∫ ω, rankTableReach G T i ω ∂rankTableInputsLaw P) = (finiteRankTableLearner G T).reachProbability P i := by
  have hEvent := measurableSet_rankTableReaches G T i
  have hInt : (∫ ω, rankTableReach G T i ω ∂rankTableInputsLaw P) =
      (rankTableInputsLaw (k := k) P).real {ω | (finiteRankTablePolicy G T).Reaches (ω.2.2,()) ω.2.1 ω.1 i} := by
    simpa only [rankTableReach,Set.indicator_apply,Set.mem_setOf_eq,smul_eq_mul,mul_one] using
      integral_indicator_const (μ := rankTableInputsLaw (k := k) P) (1 : ℝ) hEvent
  rw [hInt]
  change (rankTableInputsLaw (k := k) P).real {ω | (finiteRankTablePolicy G T).Reaches (ω.2.2,()) ω.2.1 ω.1 i} =
    (P.valuesLaw.prod ((Instance.uniformPermutationLaw n).prod ((P.reservoirLaw k).prod (Measure.dirac ())))).real
      {ω | (finiteRankTableLearner G T).policy.Reaches ω.2.2 ω.2.1 ω.1 i}
  rw [finiteRankTableLearner_policy]
  exact (congrArg ENNReal.toReal ((rankUnitInputs_measurePreserving (k := k) P).measure_preimage hEvent.nullMeasurableSet)).symm

end ProphetSecretary.Statistics
