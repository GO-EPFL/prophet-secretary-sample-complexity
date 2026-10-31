import ProphetSecretary.Model.BellmanPerformance

/-!
# Dropping reach from the actual performance identity

All admissible history-dependent policies have nonnegative local Bellman
losses. Their scalar regret is therefore bounded by the sum of the expected
potential losses at every arrival. These post-stopping quantities are purely
analytical and are not observations supplied to the executed policy.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

omit [MeasurableSpace Seed] in
lemma Policy.arrivalBellmanLoss_le_value_add (π : Policy Seed n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0≤w) (hc : 0≤c)
    (r : Seed) (x u : Fin n → ℝ) (i : Fin n) (hx : 0≤x i) (hu : 0≤u i) :
    π.arrivalBellmanLoss P w c r x u i ≤ w*x i+optimalScalarValue P w c := by
  have hX := mul_nonneg hw hx
  have hv0 := P.continuationAtArrival_nonnegative hP hw hc x u i
  have hv1 := P.continuationAtArrival_le_initial hP hw hc x u i hu
  have hm : max (w*x i) (P.continuationAtArrival w c x u i) ≤ w*x i+P.continuationAtArrival w c x u i :=
    max_le (by linarith only [hv0]) (by linarith only [hX])
  have hchoice : 0≤ if π.action r Finset.univ x u i=true then w*x i else P.continuationAtArrival w c x u i := by
    split_ifs <;> assumption
  unfold Policy.arrivalBellmanLoss
  exact (sub_le_self _ hchoice).trans (hm.trans (add_le_add le_rfl hv1))

lemma Policy.integrable_arrivalBellmanLoss (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (hP : Integrable Instance.maximum P.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0<w) (hc : 0≤c) (i : Fin n) :
    Integrable (fun ω : World n Seed => π.arrivalBellmanLoss P w c ω.2.2 ω.1 ω.2.1 i) (P.worldLaw ν) := by
  have hp : MeasurePreserving (fun ω : World n Seed => ω.1) (P.worldLaw ν) P.valuesLaw := measurePreserving_fst
  have hI : Integrable (fun ω : World n Seed => w*ω.1 i+optimalScalarValue P w c) (P.worldLaw ν) :=
    ((hp.integrable_comp_of_integrable (P.integrable_coordinate_of_maximum hP i)).const_mul w).add (integrable_const _)
  apply hI.mono' (π.measurable_arrivalBellmanLoss hπ P hP hw hc
    (measurable_snd.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i).aestronglyMeasurable
  filter_upwards [hp.quasiMeasurePreserving.ae P.ae_nonnegative,P.world_clocks_mem_unitInterval ν] with ω hx hu
  rw [Real.norm_eq_abs,abs_of_nonneg (π.arrivalBellmanLoss_nonnegative P w c _ _ _ _)]
  exact π.arrivalBellmanLoss_le_value_add P hP hw.le hc ω.2.2 ω.1 ω.2.1 i (hx i) (hu i).1

omit [MeasurableSpace Seed] in
lemma Policy.reachedBellmanLoss_le_unreached_sum (π : Policy Seed n) (P : Instance n)
    (w c : ℝ) (r : Seed) (x u : Fin n → ℝ) :
    π.reachedBellmanLoss P w c r x u ≤ ∑ i, π.arrivalBellmanLoss P w c r x u i := by
  apply Finset.sum_le_sum
  intro i _
  split_ifs
  · exact le_rfl
  · exact π.arrivalBellmanLoss_nonnegative P w c r x u i

/-- General policies, not only canonical or Markov policies, satisfy this bound. -/
theorem RandomizedPolicy.scalarRegret_le_sum_arrivalLoss (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    optimalScalarValue P w c-π.scalarObjective P w c ≤
      ∑ i, ∫ ω : π.World, π.rule.arrivalBellmanLoss P w c ω.2.2 ω.1 ω.2.1 i ∂P.worldLaw π.seedLaw := by
  rw [π.bellman_performanceDifference P hP hw hc]
  have hI (i : Fin n) := π.rule.integrable_arrivalBellmanLoss π.measurable_rule P hP π.seedLaw hw hc i
  have hm := integral_mono
    (π.rule.integrable_reachedBellmanLoss π.measurable_rule P hP π.seedLaw hw hc)
    (integrable_finsetSum _ (fun i _ => hI i))
    (fun ω : π.World => π.rule.reachedBellmanLoss_le_unreached_sum P w c ω.2.2 ω.1 ω.2.1)
  rw [integral_finsetSum _ (fun i _ => hI i)] at hm
  exact hm

end ProphetSecretary.Model
