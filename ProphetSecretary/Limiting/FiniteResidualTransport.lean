import ProphetSecretary.Limiting.HybridGeneratorVerification
import ProphetSecretary.Limiting.IgnorePoisson

/-!
# Transporting a finite policy's residual through the hybrid adapter

A finite policy rejects every anonymous arrival. The proved pathwise equality
of stopping times therefore also preserves each retained reach event. Product
projection transports its complete reached residual without assuming anything
about the future anonymous count or supplying it to the callback.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma ignorePoisson_retainedResidual (π : Model.RandomizedPolicy n) (Q P : Model.Instance n)
    (w c : ℝ) (v : HybridWorld n π.Seed) :
    (ignorePoisson π).rule.retainedDesignResidual Q P w c v =
      π.rule.reachedTransitionResidual Q P w c v.2.2.2 v.2.1 v.2.2.1 := by
  unfold HybridRule.retainedDesignResidual Model.Policy.reachedTransitionResidual
  apply Finset.sum_congr rfl
  intro i _
  have hreach : (ignorePoisson π).rule.ReachesIndividual v.2.2.2 v.2.1 v.2.2.1 v.1 i ↔
      π.rule.Reaches v.2.2.2 v.2.1 v.2.2.1 i := by
    unfold HybridRule.ReachesIndividual Model.Policy.Reaches
    simp only [combinedClocks, Fin.addCases_left]
    change v.2.2.1 i ≤ (ignorePoisson π).rule.realizedDuration v ↔ v.2.2.1 i ≤ π.realizedDuration v.2
    rw [ignorePoisson_duration]
  rw [hreach]

lemma ignorePoisson_retainedResidual_expectation (π : Model.RandomizedPolicy n) (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (hP : Integrable Model.Instance.maximum P.valuesLaw)
    (μ : FiniteMeasure ℝ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (∫ v, (ignorePoisson π).rule.retainedDesignResidual Q P w c v ∂hybridWorldLaw P μ π.seedLaw) =
      π.expectedReachedTransitionResidual Q P w c := by
  have hp : MeasurePreserving (fun v : HybridWorld n π.Seed => v.2)
      (hybridWorldLaw P μ π.seedLaw) (P.worldLaw π.seedLaw) := measurePreserving_snd
  have hm := π.rule.measurable_reachedTransitionResidual π.measurable_rule Q P hQ hP hw hc
    (r := fun ω : Model.World n π.Seed => ω.2.2) (x := fun ω => ω.1) (u := fun ω => ω.2.1)
    (by fun_prop) (fun j => by fun_prop) (fun j => by fun_prop)
  have he := integral_map (μ := hybridWorldLaw P μ π.seedLaw) hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  calc
    _ = ∫ v : HybridWorld n π.Seed, π.rule.reachedTransitionResidual Q P w c v.2.2.2 v.2.1 v.2.2.1
        ∂hybridWorldLaw P μ π.seedLaw :=
      integral_congr_ae (Filter.Eventually.of_forall (ignorePoisson_retainedResidual π Q P w c))
    _ = _ := he.symm

/-- Every actual finite policy has the same derived retained-generator identity,
with an independent anonymous configuration added only analytically. -/
theorem finite_reachedResidual_eq_hybridDrift (π : Model.RandomizedPolicy n) (Q P : Model.Instance n)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (hP : Integrable Model.Instance.maximum P.valuesLaw)
    (μ : FiniteMeasure ℝ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    π.expectedReachedTransitionResidual Q P w c =
      ∫ v, ∫ t, (ignorePoisson π).rule.retainedPotentialDrift Q P w c (v,t)
        ∂Model.Instance.uniformClock ∂hybridWorldLaw P μ π.seedLaw := by
  rw [← ignorePoisson_retainedResidual_expectation π Q P hQ hP μ hw hc]
  exact ((ignorePoisson π).rule.retainedDesignResidual_expectation_eq_drift
    (ignorePoisson π).measurable_rule Q P hQ hP μ (ignorePoisson π).seedLaw hw hc).2

end ProphetSecretary.Limiting
