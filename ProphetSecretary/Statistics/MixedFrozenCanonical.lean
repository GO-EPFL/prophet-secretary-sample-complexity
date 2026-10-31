import ProphetSecretary.Model.MixedEmpiricalLearner

/-!
# Exact frozen mixed learner decisions under every evaluation law

The training outcome and auxiliary seed are fixed before evaluating the online
instance. Exact equality on every history identifies the frozen rule with the
canonical mixed optimizer, including off its design-law support. The resulting
objective equality is valid under an arbitrary separate evaluation instance.
-/

open MeasureTheory
open scoped Classical
namespace ProphetSecretary.Model
variable {n k : ℕ} [NeZero k]

lemma Learner.mixedEmpiricalWithSelectedWeights_frozen_rule_eq (D : Instance n)
    (hD : Integrable Instance.maximum D.valuesLaw) (known : Finset (Fin n)) (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C)
    (y : Reservoir n k) (r : Seed) (hw : 0<W (y,r)) (hc : 0≤C (y,r)) :
    (Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν W C hW hC).frozenRule y r =
      ((mixedEmpiricalInstance D known y).valuePolicy (mixedEmpiricalInstance_integrable D hD known y) hw.le hc).rule := by
  have hdec : ((Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν W C hW hC).frozenRule y r).decide =
      ((mixedEmpiricalInstance D known y).valuePolicy (mixedEmpiricalInstance_integrable D hD known y) hw.le hc).rule.decide := by
    funext s t i x h
    cases s
    exact Learner.mixedEmpiricalWithSelectedWeights_decide D hD known Seed ν W C hW hC y r hw hc t i x h
  exact congrArg Policy.mk hdec

/-- Evaluation-law transfer follows from exact decisions, not just design-law
optimality. Both objectives retain the same physical duration convention. -/
theorem Learner.mixedEmpiricalWithSelectedWeights_frozen_objective_eq (D : Instance n)
    (hD : Integrable Instance.maximum D.valuesLaw) (known : Finset (Fin n)) (Seed : Type) [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (W C : Reservoir n k × Seed → ℝ) (hW : Measurable W) (hC : Measurable C)
    (y : Reservoir n k) (r : Seed) (hw : 0<W (y,r)) (hc : 0≤C (y,r))
    (P : Instance n) (w c : ℝ) :
    ((Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν W C hW hC).frozenRandomizedPolicy y r).scalarObjective P w c =
      ((mixedEmpiricalInstance D known y).valuePolicy (mixedEmpiricalInstance_integrable D hD known y) hw.le hc).scalarObjective P w c := by
  have hRule := Learner.mixedEmpiricalWithSelectedWeights_frozen_rule_eq D hD known Seed ν W C hW hC y r hw hc
  change (∫ ω : World n Unit,
    w*((Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν W C hW hC).frozenRule y r).reward ω.2.2 Finset.univ ω.1 ω.2.1 +
    c*((Learner.mixedEmpiricalWithSelectedWeights D hD known Seed ν W C hW hC).frozenRule y r).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1
    ∂P.worldLaw (Measure.dirac ())) = _
  rw [hRule]
  rfl

end ProphetSecretary.Model
