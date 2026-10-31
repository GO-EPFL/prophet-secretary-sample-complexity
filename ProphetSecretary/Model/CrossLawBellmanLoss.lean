import ProphetSecretary.Model.UnreachedBellmanLoss
import ProphetSecretary.Model.BellmanResidual

/-!
# Bellman action losses under a separate evaluation law

The target law supplies the continuation value, while online observations have
a different independent product law. Nonnegativity and a value-plus-offer bound
give genuine integrability under that evaluation law. This distinction is used
when a fixed true optimizer incurs mixed-design action loss on true online offers.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Model
variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Policy.integrable_arrivalBellmanLoss_under (π : Policy Seed n) (hπ : π.IsMeasurable)
    (T E : Instance n) (hT : Integrable Instance.maximum T.valuesLaw)
    (hE : Integrable Instance.maximum E.valuesLaw) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {w c : ℝ} (hw : 0<w) (hc : 0≤c) (i : Fin n) :
    Integrable (fun ω : World n Seed => π.arrivalBellmanLoss T w c ω.2.2 ω.1 ω.2.1 i) (E.worldLaw ν) := by
  have hp : MeasurePreserving (fun ω : World n Seed => ω.1) (E.worldLaw ν) E.valuesLaw := measurePreserving_fst
  have hI : Integrable (fun ω : World n Seed => w*ω.1 i+optimalScalarValue T w c) (E.worldLaw ν) :=
    ((hp.integrable_comp_of_integrable (E.integrable_coordinate_of_maximum hE i)).const_mul w).add (integrable_const _)
  apply hI.mono' (π.measurable_arrivalBellmanLoss hπ T hT hw hc
    (measurable_snd.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst)
    (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd)) i).aestronglyMeasurable
  filter_upwards [hp.quasiMeasurePreserving.ae E.ae_nonnegative,E.world_clocks_mem_unitInterval ν] with ω hx hu
  change ‖π.arrivalBellmanLoss T w c ω.2.2 ω.1 ω.2.1 i‖≤_
  rw [Real.norm_eq_abs,abs_of_nonneg (π.arrivalBellmanLoss_nonnegative T w c _ _ _ _)]
  exact π.arrivalBellmanLoss_le_value_add T hT hw.le hc ω.2.2 ω.1 ω.2.1 i (hx i) (hu i).1

/-- Dropping true evaluation-law reach does not require the target law to equal
that evaluation law. The policy may use its full admissible history and seed. -/
theorem RandomizedPolicy.expectedDesignActionLoss_le_sum_arrivalLoss_under (π : RandomizedPolicy n)
    (T E : Instance n) (hT : Integrable Instance.maximum T.valuesLaw)
    (hE : Integrable Instance.maximum E.valuesLaw) {w c : ℝ} (hw : 0<w) (hc : 0≤c) :
    π.expectedReachedDesignActionLoss T E w c ≤
      ∑ i, ∫ ω : π.World, π.rule.arrivalBellmanLoss T w c ω.2.2 ω.1 ω.2.1 i ∂E.worldLaw π.seedLaw := by
  have hI (i : Fin n) := π.rule.integrable_arrivalBellmanLoss_under π.measurable_rule T E hT hE π.seedLaw hw hc i
  have hUpper : Integrable (fun ω : π.World => ∑ i : Fin n,
      π.rule.arrivalBellmanLoss T w c ω.2.2 ω.1 ω.2.1 i) (E.worldLaw π.seedLaw) :=
    integrable_finsetSum Finset.univ (fun i _ => hI i)
  have hR : Integrable (fun ω : π.World => π.rule.reachedBellmanLoss T w c ω.2.2 ω.1 ω.2.1) (E.worldLaw π.seedLaw) := by
    apply hUpper.mono' (π.rule.measurable_reachedBellmanLoss π.measurable_rule T hT hw hc
      (measurable_snd.comp measurable_snd) (fun j => (measurable_pi_apply j).comp measurable_fst)
      (fun j => (measurable_pi_apply j).comp (measurable_fst.comp measurable_snd))).aestronglyMeasurable
    exact Eventually.of_forall fun ω => by
      change ‖π.rule.reachedBellmanLoss T w c ω.2.2 ω.1 ω.2.1‖≤_
      rw [Real.norm_eq_abs,abs_of_nonneg (π.rule.reachedBellmanLoss_nonnegative T w c _ _ _)]
      exact π.rule.reachedBellmanLoss_le_unreached_sum T w c _ _ _
  have h := integral_mono hR hUpper (fun ω : π.World =>
    π.rule.reachedBellmanLoss_le_unreached_sum T w c ω.2.2 ω.1 ω.2.1)
  rw [integral_finsetSum _ (fun i _ => hI i)] at h
  exact h

end ProphetSecretary.Model
