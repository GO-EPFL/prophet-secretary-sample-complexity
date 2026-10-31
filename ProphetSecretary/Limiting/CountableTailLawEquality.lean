import ProphetSecretary.Limiting.CountableIndividualSplit
import ProphetSecretary.Limiting.CountableIndividualOmission

/-!
# Omitted-tail expectations depend only on the omitted marginals

The actual infinite tail law is the independent product of its marginals.
Equal reserves and equal marginals after the retained prefix therefore give
the same expected omitted excess maximum, regardless of changes to earlier
individual laws or to the anonymous intensity.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting.CountableInstance

theorem expectedIndividualTailExcessMaximum_eq_of_tail_laws (B D : CountableInstance) (N : ℕ)
    (hTerminal : D.terminal=B.terminal)
    (hTail : ∀ i : ℕ, N ≤ i → D.individuals i=B.individuals i) :
    D.expectedIndividualTailExcessMaximum N=B.expectedIndividualTailExcessMaximum N := by
  let F : (ℕ → ℝ) → ℝ := fun x => countableMaximum 0 (fun k => Model.excessValueMap B.terminal (x k))
  have hF : Measurable F := measurable_countableMaximum 0 (fun k =>
    (Model.measurable_excessValueMap B.terminal).comp (measurable_pi_apply k))
  have hLaw : D.tailValuesLaw N=B.tailValuesLaw N := by
    change Measure.infinitePi (fun k => (D.individuals (k+N) : Measure ℝ))=
      Measure.infinitePi (fun k => (B.individuals (k+N) : Measure ℝ))
    congr 1
    funext k
    rw [hTail (k+N) (by omega)]
  have hB : B.expectedIndividualTailExcessMaximum N=∫ x, F x ∂B.tailValuesLaw N :=
    (B.tailValues_measurePreserving N).hasLaw.integral_comp hF.aestronglyMeasurable
  have hD : D.expectedIndividualTailExcessMaximum N=∫ x, F x ∂D.tailValuesLaw N := by
    unfold expectedIndividualTailExcessMaximum individualTailExcessMaximum
    rw [hTerminal]
    exact (D.tailValues_measurePreserving N).hasLaw.integral_comp hF.aestronglyMeasurable
  rw [hD,hLaw]
  exact hB.symm

end ProphetSecretary.Limiting.CountableInstance
