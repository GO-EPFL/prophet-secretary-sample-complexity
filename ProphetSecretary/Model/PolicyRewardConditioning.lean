import ProphetSecretary.Model.LearnerConditioning

/-!
# Averaging a fixed policy's independent seed

Product Fubini expresses the policy reward as the average of its online
expectations with each seed fixed. Integrability follows from the original
finite expected maximum, without bounded offers.
-/

open MeasureTheory
namespace ProphetSecretary.Model
variable {n : ℕ}

lemma RandomizedPolicy.integral_seedFirstReward (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    (∫ r, ∫ ω : ProphetSecretary.Model.World n Unit, π.rule.reward r Finset.univ ω.1 ω.2.1
      ∂P.worldLaw (Measure.dirac ()) ∂π.seedLaw)=π.expectedReward P := by
  have hMP := P.seedFirstWorld_measurePreserving π.seedLaw
  have hInt := hMP.integrable_comp_of_integrable (π.integrable_realizedReward P hP)
  have hMap := integral_map (μ:=π.seedLaw.prod (P.worldLaw (Measure.dirac ())))
    hMP.measurable.aemeasurable π.measurable_realizedReward.aestronglyMeasurable
  rw [hMP.map_eq] at hMap
  have hFub := integral_prod (fun p : π.Seed × ProphetSecretary.Model.World n Unit =>
    π.rule.reward p.1 Finset.univ p.2.1 p.2.2.1) hInt
  exact hFub.symm.trans hMap.symm

end ProphetSecretary.Model
