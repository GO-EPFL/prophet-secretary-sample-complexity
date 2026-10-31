import ProphetSecretary.Probability.JackpotCoupling
import ProphetSecretary.Model.BellmanOptimal
import Mathlib.Probability.Independence.Integration

/-!
# Reward controlled by duration and total first moment

Paper correspondence: the unnamed intermediate comparison in `upstat:duration`.
The constant two is uniform in the number of offers. The policy need not be Markov.
-/

open MeasureTheory Set ProbabilityTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*}

lemma Policy.reward_le_reached_sum (π : Policy Seed n) (r : Seed) (x u : Fin n → ℝ)
    (hx : ∀ i, 0 ≤ x i) :
    π.reward r Finset.univ x u ≤ ∑ i, x i * (if π.Reaches r x u i then 1 else 0) := by
  apply Finset.sum_le_sum
  intro i _
  by_cases ha : π.ActualSelects r Finset.univ x u i
  · have hr := π.selects_implies_reaches r x u ha.1
    simp only [if_pos ha, if_pos hr, mul_one, le_refl]
  · rw [if_neg ha]
    split_ifs <;> simp_all

/-- No finite-support, threshold, or optimizer restriction is imposed. -/
theorem RandomizedPolicy.expectedReward_le_twice_duration_mul_firstMoment
    (π : RandomizedPolicy n) (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) :
    π.expectedReward P ≤ 2 * π.expectedDuration P * P.totalFirstMoment := by
  classical
  let μ := P.worldLaw π.seedLaw
  let I : Fin n → π.World → ℝ := fun i ω => if π.rule.Reaches ω.2.2 ω.1 ω.2.1 i then 1 else 0
  have hXi (i : Fin n) : Integrable (fun ω : π.World => ω.1 i) μ :=
    ((measurePreserving_eval P.law i).comp measurePreserving_fst).integrable_comp_of_integrable
      (P.integrable_maximum_iff.mp hP i)
  have hIm (i : Fin n) : Measurable (I i) := Measurable.ite
    (π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
      (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i)
    measurable_const measurable_const
  have hIi (i : Fin n) : Integrable (I i) μ := by
    apply Integrable.of_bound (hIm i).aestronglyMeasurable 1
    filter_upwards [] with ω
    dsimp [I]
    split_ifs <;> norm_num
  have hi (i : Fin n) := ProphetSecretary.Probability.reachIndicator_value_independent P π.seedLaw i π.rule π.measurable_rule
  have hprod (i : Fin n) : Integrable (fun ω : π.World => ω.1 i * I i ω) μ :=
    (hi i).symm.integrable_mul (hXi i) (hIi i)
  have hfactor (i : Fin n) : (∫ ω : π.World, ω.1 i * I i ω ∂μ) =
      (∫ x, x ∂P.law i) * π.rule.reachProbability P π.seedLaw i := by
    have h := (hi i).symm.integral_fun_mul_eq_mul_integral (hXi i).aestronglyMeasurable (hIi i).aestronglyMeasurable
    have hv : MeasurePreserving (fun ω : π.World => ω.1 i) μ (P.law i) :=
      (measurePreserving_eval P.law i).comp measurePreserving_fst
    have hX := integral_map (μ := μ) hv.measurable.aemeasurable aestronglyMeasurable_id
    rw [hv.map_eq] at hX
    change (∫ x : ℝ, x ∂P.law i) = ∫ ω : π.World, ω.1 i ∂μ at hX
    have hR : (∫ ω, I i ω ∂μ) = π.rule.reachProbability P π.seedLaw i := by
      simpa only [I, μ, Policy.reachProbability, Set.indicator_apply, Pi.one_apply,
        Set.mem_setOf_eq, Function.comp_def] using (integral_indicator_one (μ := μ)
        (π.rule.measurableSet_reaches π.measurable_rule (measurable_snd.comp measurable_snd)
          (fun j => (measurable_pi_apply j).comp measurable_fst)
          (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i))
    change (∫ ω : π.World, ω.1 i * I i ω ∂μ) = (∫ ω : π.World, ω.1 i ∂μ) * (∫ ω : π.World, I i ω ∂μ) at h
    rw [← hX, hR] at h
    exact h
  have hvalues : ∀ᵐ ω : π.World ∂μ, ∀ i, 0 ≤ ω.1 i :=
    (measurePreserving_fst : MeasurePreserving (fun ω : π.World => ω.1) μ P.valuesLaw).quasiMeasurePreserving.ae
      P.ae_nonnegative
  have hsum := integral_mono_ae (π.integrable_realizedReward P hP)
    (integrable_finsetSum Finset.univ (fun i _ => hprod i)) (by
      filter_upwards [hvalues] with ω hω
      exact π.rule.reward_le_reached_sum _ _ _ hω)
  rw [integral_finsetSum Finset.univ (fun i _ => hprod i)] at hsum
  simp only [hfactor] at hsum
  apply hsum.trans
  calc
    (∑ i, (∫ x, x ∂P.law i) * π.rule.reachProbability P π.seedLaw i) ≤
        ∑ i, (∫ x, x ∂P.law i) * (2 * π.expectedDuration P) := by
      apply Finset.sum_le_sum
      intro i _
      have hq : π.rule.reachProbability P π.seedLaw i ≤ 2 * π.expectedDuration P :=
        π.rule.reachProbability_le_twice_meanDuration π.measurable_rule P π.seedLaw i
      exact mul_le_mul_of_nonneg_left hq (integral_nonneg_of_ae (P.nonnegative i))
    _ = 2 * π.expectedDuration P * P.totalFirstMoment := by
      rw [← Finset.sum_mul]
      unfold Instance.totalFirstMoment
      ring

/-- The canonical state's value is controlled by its normalized duration and first moment. -/
lemma Instance.valuePolicy_value_le_duration (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    optimalScalarValue P w c ≤
      (P.valuePolicy hP hw.le hc).expectedDuration P * (2 * w * P.totalFirstMoment + c) := by
  let π := P.valuePolicy hP hw.le hc
  have hR := π.expectedReward_le_twice_duration_mul_firstMoment P hP
  have hwR := mul_le_mul_of_nonneg_left hR hw.le
  have hJ : π.scalarObjective P w c = optimalScalarValue P w c := P.valuePolicy_optimal hP hw hc
  rw [π.scalarObjective_eq P hP] at hJ
  nlinarith

end ProphetSecretary.Model

