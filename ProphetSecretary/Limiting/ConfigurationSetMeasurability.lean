import ProphetSecretary.Limiting.ConfigurationMeasurability

/-!
# Measurable events across configuration branches

A finite-array event is measurable on the countable configuration disjoint
union exactly when each fixed-count branch is measurable. The count remains
an analytical coordinate and is not an additional observation of a policy.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting

lemma measurableSet_of_configuration_prod_branches {Seed : Type*} [MeasurableSpace Seed]
    (E : Set (World Seed))
    (hE : ∀ N, MeasurableSet {v : (Fin N → Point) × Seed | (configurationMk N v.1,v.2) ∈ E}) :
    MeasurableSet E := by
  have hI : Measurable (E.indicator (fun _ => (1 : ℝ))) := by
    apply measurable_of_configuration_prod_branches
    intro N
    exact measurable_const.indicator (hE N)
  exact (measurable_indicator_const_iff (1 : ℝ)).mp hI

end ProphetSecretary.Limiting
