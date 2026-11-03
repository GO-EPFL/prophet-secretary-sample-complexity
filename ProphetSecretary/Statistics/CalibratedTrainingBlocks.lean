import ProphetSecretary.Probability.ProductCoordinates
import ProphetSecretary.Statistics.TrainingColumns
import ProphetSecretary.Model.AllSamplesLearner

/-!
# The two independent training blocks of the calibrated learner

The first and second `m` observations of each marginal are projected from the
actual `2m`-sample reservoir. Their joint product law is proved from the
injective coordinate projection. Transposing the second block then gives
independent complete-instance validation vectors.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m : ℕ}

def blockIndex : (Fin n × Fin m) ⊕ (Fin n × Fin m) → (Fin n × Fin (2*m))
  | .inl q => (q.1, ⟨q.2.val, by omega⟩)
  | .inr q => (q.1, ⟨m+q.2.val, by omega⟩)

lemma blockIndex_injective : Function.Injective (@blockIndex n m) := by
  intro a b hab
  cases a with
  | inl a =>
    cases b with
    | inl b =>
      apply congrArg Sum.inl
      apply Prod.ext
      · exact congrArg (fun q : Fin n × Fin (2*m) => q.1) hab
      · apply Fin.ext
        exact congrArg (fun q : Fin n × Fin (2*m) => q.2.val) hab
    | inr b =>
      have h := congrArg (fun q : Fin n × Fin (2*m) => q.2.val) hab
      simp only [blockIndex] at h
      have ha := a.2.is_lt
      omega
  | inr a =>
    cases b with
    | inl b =>
      have h := congrArg (fun q : Fin n × Fin (2*m) => q.2.val) hab
      simp only [blockIndex] at h
      have hb := b.2.is_lt
      omega
    | inr b =>
      apply congrArg Sum.inr
      apply Prod.ext
      · exact congrArg (fun q : Fin n × Fin (2*m) => q.1) hab
      · apply Fin.ext
        have h := congrArg (fun q : Fin n × Fin (2*m) => q.2.val) hab
        simp only [blockIndex] at h
        omega

def blockEmbedding : ((Fin n × Fin m) ⊕ (Fin n × Fin m)) ↪ (Fin n × Fin (2*m)) :=
  ⟨blockIndex, blockIndex_injective⟩

/-- The literal first and second blocks, before any empirical transformation. -/
def splitTrainingArray (a : (Fin n × Fin (2*m)) → ℝ) :
    ((Fin n × Fin m) → ℝ) × ((Fin n × Fin m) → ℝ) :=
  (fun q => a (blockIndex (.inl q)), fun q => a (blockIndex (.inr q)))

lemma measurable_splitTrainingArray : Measurable (@splitTrainingArray n m) := by
  exact (measurable_pi_lambda _ (fun q => measurable_pi_apply (blockIndex (.inl q)))).prodMk
    (measurable_pi_lambda _ (fun q => measurable_pi_apply (blockIndex (.inr q))))

/-- The training blocks are independent because they are disjoint actual coordinates. -/
lemma splitTrainingArray_measurePreserving (P : Instance n) :
    MeasurePreserving (splitTrainingArray (n := n) (m := m)) (P.trainingCoordinateLaw (2*m))
      ((P.trainingCoordinateLaw m).prod (P.trainingCoordinateLaw m)) := by
  have hp := productCoordinateProjection_measurePreserving
    (fun q : Fin n × Fin (2*m) => P.law q.1) (blockEmbedding (n := n) (m := m))
  have hs := measurePreserving_sumPiEquivProdPi
    (fun q : (Fin n × Fin m) ⊕ (Fin n × Fin m) => P.law (blockIndex q).1)
  exact hs.comp hp

/-- The second block supplies `m` iid online-value profiles, independent of the first block. -/
def trainingAndValidation (y : Reservoir n (2*m)) :
    ((Fin n × Fin m) → ℝ) × (Fin m → (Fin n → ℝ)) :=
  let a := splitTrainingArray (reservoirCoordinates y)
  (a.1, fun j i => a.2 (i,j))

lemma trainingAndValidation_measurePreserving (P : Instance n) :
    MeasurePreserving (trainingAndValidation (n := n) (m := m)) (P.reservoirLaw (2*m))
      ((P.trainingCoordinateLaw m).prod (Measure.pi (fun _ : Fin m => P.valuesLaw))) := by
  exact ((MeasurePreserving.id (P.trainingCoordinateLaw m)).prod
    (trainingColumns_measurePreserving (k := m) P)).comp
      ((splitTrainingArray_measurePreserving (m := m) P).comp
        (P.reservoirCoordinates_measurePreserving (2*m)))

end ProphetSecretary.Statistics.Calibration
