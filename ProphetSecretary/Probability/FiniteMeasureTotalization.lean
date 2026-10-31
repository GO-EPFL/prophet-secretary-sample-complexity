import Mathlib.MeasureTheory.Measure.FiniteMeasure

/-!
# A measurable finite-measure totalization

The totalization equals its argument whenever the latter is finite and equals
zero otherwise. It permits finite-measure-valued payoff functionals to be
composed with an analytical random measure whose finiteness is proved almost
surely, without adding an assumption on every raw training or online outcome.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

variable {α : Type*} [MeasurableSpace α]

noncomputable def finiteMeasureOrZero (μ : Measure α) : FiniteMeasure α :=
  if h : IsFiniteMeasure μ then ⟨μ,h⟩ else 0

lemma measurable_finiteMeasureOrZero : Measurable (finiteMeasureOrZero (α := α)) := by
  have hgood : Measurable (fun q : {μ : Measure α // IsFiniteMeasure μ} => (⟨q.1,q.2⟩ : FiniteMeasure α)) :=
    measurable_subtype_coe.subtype_mk
  exact Measurable.dite hgood measurable_const FiniteMeasure.measurableSet_isFiniteMeasure

lemma finiteMeasureOrZero_coe (μ : Measure α) (hμ : IsFiniteMeasure μ) :
    (finiteMeasureOrZero μ : Measure α) = μ := by
  rw [finiteMeasureOrZero,dif_pos hμ]
  rfl

end ProphetSecretary.Probability
