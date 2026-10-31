import ProphetSecretary.Model.TrainingBlockSplit
import ProphetSecretary.Model.EmpiricalCapPolicy
import ProphetSecretary.Model.TrainingZeroSimulation

/-!
# A law-independent learner using an empirical training block

The learner requests its full training reservoir, estimates the empirical
law from the chosen columns, and may select its scalar from all observed
training data. The split seed equivalence reconstructs those data from the
empirical block and the independent remainder. Only the analytical law of
the remainder depends on the true instance; the learner does not.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n m c : ℕ} {Seed : Type} [MeasurableSpace Seed]

noncomputable def trainingBlockSeedEquiv (e : Fin m ↪ Fin c) :
    (Reservoir n c × Seed) ≃ᵐ (Reservoir n m × ((TrainingRemainderIndex n e → ℝ) × Seed)) :=
  ((splitTrainingBlock e).prodCongr (MeasurableEquiv.refl Seed)).trans MeasurableEquiv.prodAssoc

lemma Instance.trainingBlockSeedEquiv_measurePreserving (P : Instance n) (e : Fin m ↪ Fin c)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (trainingBlockSeedEquiv e) ((P.reservoirLaw c).prod ν)
      ((P.reservoirLaw m).prod ((P.trainingRemainderLaw e).prod ν)) :=
  (measurePreserving_prodAssoc (P.reservoirLaw m) (P.trainingRemainderLaw e) ν).comp
    ((P.splitTrainingBlock_measurePreserving e).prod (MeasurePreserving.id ν))

noncomputable def trainingBlockScalar (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) :
    Reservoir n m × ((TrainingRemainderIndex n e → ℝ) × Seed) → ℝ :=
  fun p => Z ((trainingBlockSeedEquiv e).symm p)

lemma measurable_trainingBlockScalar (e : Fin m ↪ Fin c) {Z : Reservoir n c × Seed → ℝ} (hZ : Measurable Z) :
    Measurable (trainingBlockScalar e Z) := hZ.comp (trainingBlockSeedEquiv e).symm.measurable

variable [NeZero m]

noncomputable def empiricalTrainingBlockPolicy (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) :
    Policy (Reservoir n c × Seed) n :=
  (empiricalCapSelectedPolicy (trainingBlockScalar e Z)).comapSeed (trainingBlockSeedEquiv e)

lemma empiricalTrainingBlockPolicy_isMeasurable (e : Fin m ↪ Fin c)
    {Z : Reservoir n c × Seed → ℝ} (hZ : Measurable Z) : (empiricalTrainingBlockPolicy e Z).IsMeasurable :=
  Policy.comapSeed_isMeasurable (trainingBlockSeedEquiv e).measurable _
    (empiricalCapSelectedPolicy_isMeasurable (measurable_trainingBlockScalar e hZ))

noncomputable def Learner.empiricalTrainingBlock (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z) : Learner n c :=
  Learner.ofSamplePolicy Seed ν (empiricalTrainingBlockPolicy e Z) (empiricalTrainingBlockPolicy_isMeasurable e hZ)

lemma Learner.empiricalTrainingBlock_decide (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n c) (r : Seed) (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    (Learner.empiricalTrainingBlock ν e Z hZ).policy.decide (y,r) t i x H =
      Decidable.decide (0<x ∧ empiricalCapThreshold (splitTrainingBlock e y).1 (Z (y,r)) (unseen H) t i≤x) := by
  change (Learner.ofSamplePolicy Seed ν (empiricalTrainingBlockPolicy e Z)
    (empiricalTrainingBlockPolicy_isMeasurable e hZ)).policy.decide (y,r) t i x H=_
  rw [Learner.ofSamplePolicy_decide]
  change Decidable.decide (0<x ∧ empiricalCapThreshold (splitTrainingBlock e y).1
    (Z ((trainingBlockSeedEquiv e).symm (trainingBlockSeedEquiv e (y,r)))) (unseen H) t i≤x)=_
  rw [MeasurableEquiv.symm_apply_apply]

lemma Learner.empiricalTrainingBlock_requests_eq (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n c) (r : Seed) (i : Fin n) :
    requests (trainingTranscript (Learner.empiricalTrainingBlock ν e Z hZ).request r y) i=c :=
  train_requestAll_full r y (n*c) [] (by simp [WithinBudget]) (by simp) i

end ProphetSecretary.Model
