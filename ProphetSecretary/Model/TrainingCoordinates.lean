import ProphetSecretary.Model.TrainingLaw
import Mathlib.MeasureTheory.MeasurableSpace.Embedding

/-!
# Independent individual training coordinates

Flattening the reservoir is a measurable equivalence and preserves its actual product
law. It is used only to analyze the reverse revelation of fresh samples; the learner
continues to receive its causal sampling transcript.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ}

def reservoirCoordinates : Reservoir n k ≃ᵐ ((Fin n × Fin k) → ℝ) :=
  (MeasurableEquiv.curry (Fin n) (Fin k) ℝ).symm

noncomputable def Instance.trainingCoordinateLaw (P : Instance n) (k : ℕ) :
    Measure ((Fin n × Fin k) → ℝ) := Measure.pi (fun q : Fin n × Fin k => P.law q.1)

instance Instance.trainingCoordinateLaw_probability (P : Instance n) (k : ℕ) :
    IsProbabilityMeasure (P.trainingCoordinateLaw k) := by
  unfold Instance.trainingCoordinateLaw
  infer_instance

/-- All training coordinates are independent, including coordinates from the same
marginal. The flattening law is proved on finite measurable boxes. -/
lemma Instance.reservoirCoordinates_measurePreserving (P : Instance n) (k : ℕ) :
    MeasurePreserving (reservoirCoordinates (n := n) (k := k)) (P.reservoirLaw k) (P.trainingCoordinateLaw k) := by
  have hm := (reservoirCoordinates (n := n) (k := k)).measurable
  refine ⟨hm, ?_⟩
  haveI : IsProbabilityMeasure ((P.reservoirLaw k).map reservoirCoordinates) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : reservoirCoordinates ⁻¹' Set.univ.pi s =
      Set.univ.pi (fun i : Fin n => Set.univ.pi (fun j : Fin k => s (i, j))) := by
    ext y
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left]
    constructor
    · intro h i j
      exact h (i, j)
    · intro h q
      exact h q.1 q.2
  rw [he, Instance.reservoirLaw, Measure.pi_pi]
  simp only [Measure.pi_pi]
  rw [← Finset.univ_product_univ, Finset.prod_product]

lemma Instance.reservoirCoordinates_symm_measurePreserving (P : Instance n) (k : ℕ) :
    MeasurePreserving (reservoirCoordinates (n := n) (k := k)).symm
      (P.trainingCoordinateLaw k) (P.reservoirLaw k) :=
  (P.reservoirCoordinates_measurePreserving k).symm reservoirCoordinates

end ProphetSecretary.Model
