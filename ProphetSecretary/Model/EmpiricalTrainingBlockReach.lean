import ProphetSecretary.Model.EmpiricalTrainingBlock
import ProphetSecretary.Reach.MarkovStrict

/-!
# Reach and raw action rules of the actual empirical-block learner

All training data are fixed before online play. The selected scalar may
use every training observation, while deletion monotonicity concerns only
the online unseen set. Thus true reach dominates duration under any
independent data law, without restricting the competing policy class.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model
variable {n m c : ℕ} [NeZero m] {Seed : Type} [MeasurableSpace Seed]

lemma Learner.empiricalTrainingBlock_policy (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z) :
    (Learner.empiricalTrainingBlock ν e Z hZ).policy=empiricalTrainingBlockPolicy e Z := by
  apply congrArg Policy.mk
  funext p t i x H
  exact Learner.ofSamplePolicy_decide Seed ν (empiricalTrainingBlockPolicy e Z)
    (empiricalTrainingBlockPolicy_isMeasurable e hZ) p.1 p.2 t i x H

lemma Learner.empiricalTrainingBlock_accepts_cap (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n c) (r : Seed) {t : ℝ} (ht : 0≤t) (h0 : 0≤Z (y,r)) (h1 : Z (y,r)≤1/4)
    (i : Fin n) (H : History n) : (Learner.empiricalTrainingBlock ν e Z hZ).policy.decide (y,r) t i 1 H=true := by
  rw [Learner.empiricalTrainingBlock_decide]
  exact decide_eq_true ⟨zero_lt_one,empiricalCapThreshold_le_one (splitTrainingBlock e y).1 h0 h1 ht (unseen H) i⟩

lemma Learner.empiricalTrainingBlock_rejects_zero (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z)
    (y : Reservoir n c) (r : Seed) (t : ℝ) (i : Fin n) (H : History n) :
    (Learner.empiricalTrainingBlock ν e Z hZ).policy.decide (y,r) t i 0 H=false := by
  rw [Learner.empiricalTrainingBlock_decide]
  simp

theorem Learner.empiricalTrainingBlock_meanDuration_le_reach_under (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z)
    (P : Instance n) (D : Measure (Reservoir n c × Seed)) [IsProbabilityMeasure D] (i : Fin n) :
    (Learner.empiricalTrainingBlock ν e Z hZ).policy.meanDuration P D≤
      (Learner.empiricalTrainingBlock ν e Z hZ).policy.reachProbability P D i := by
  rw [Learner.empiricalTrainingBlock_policy]
  have hMono : DeletionMonotoneAcceptance (fun p A t j x =>
      Decidable.decide (0<x ∧ empiricalCapThreshold (trainingBlockSeedEquiv e p).1
        (trainingBlockScalar e Z (trainingBlockSeedEquiv e p)) A t j≤x)) := by
    intro p t ht j x hx A B hj hAB hAccept
    exact empiricalCapSelectedPolicy_deletionMonotone (trainingBlockScalar e Z)
      (trainingBlockSeedEquiv e p) t ht j x hx A B hj hAB hAccept
  exact markovPolicy.meanDuration_le_reachProbability _ hMono (empiricalTrainingBlockPolicy_isMeasurable e hZ) P D i

end ProphetSecretary.Model
