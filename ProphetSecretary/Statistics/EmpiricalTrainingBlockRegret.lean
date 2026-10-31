import ProphetSecretary.Model.EmpiricalTrainingBlock
import ProphetSecretary.Statistics.EmpiricalCapRegret
import Mathlib.Probability.HasLaw

/-!
# Selected-scalar regret on a genuine independent training block

The whole visible reservoir may choose the scalar. The actual product-law
split, proved separately, supplies the independent remainder used only in
the analysis. The implemented learner and its auxiliary law are fixed
before the unknown instance. The error depends on the block size m,
while its hard sampling budget is the full visible reservoir size c.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Model
variable {n m c : ℕ} [NeZero m] {Seed : Type} [MeasurableSpace Seed]

lemma Learner.empiricalTrainingBlock_frozen_scalar_eq (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z)
    (η : Measure ((TrainingRemainderIndex n e → ℝ) × Seed)) [IsProbabilityMeasure η]
    (P : Instance n) (p : Reservoir n c × Seed) (w z : ℝ) :
    ((Learner.empiricalTrainingBlock ν e Z hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P w z =
      ((Learner.empiricalCapAcceptance ((TrainingRemainderIndex n e → ℝ) × Seed) η
        (trainingBlockScalar e Z) (measurable_trainingBlockScalar e hZ)).frozenRandomizedPolicy
          (trainingBlockSeedEquiv e p).1 (trainingBlockSeedEquiv e p).2).scalarObjective P w z := by
  let A := Learner.empiricalTrainingBlock ν e Z hZ
  let B := Learner.empiricalCapAcceptance ((TrainingRemainderIndex n e → ℝ) × Seed) η
    (trainingBlockScalar e Z) (measurable_trainingBlockScalar e hZ)
  have hDec : (A.frozenRule p.1 p.2).decide=
      (B.frozenRule (trainingBlockSeedEquiv e p).1 (trainingBlockSeedEquiv e p).2).decide := by
    funext s t i x H
    have hA := Learner.ofSamplePolicy_decide Seed ν (empiricalTrainingBlockPolicy e Z)
      (empiricalTrainingBlockPolicy_isMeasurable e hZ) p.1 p.2 t i x H
    have hB := Learner.empiricalCapAcceptance_decide ((TrainingRemainderIndex n e → ℝ) × Seed) η
      (trainingBlockScalar e Z) (measurable_trainingBlockScalar e hZ)
      (trainingBlockSeedEquiv e p).1 (trainingBlockSeedEquiv e p).2 t i x H
    exact hA.trans hB.symm
  have hRule : A.frozenRule p.1 p.2=
      B.frozenRule (trainingBlockSeedEquiv e p).1 (trainingBlockSeedEquiv e p).2 := congrArg Policy.mk hDec
  change (∫ ω : World n Unit, w*(A.frozenRule p.1 p.2).reward ω.2.2 Finset.univ ω.1 ω.2.1+
    z*(A.frozenRule p.1 p.2).stoppingTime ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ())) =
    (∫ ω : World n Unit, w*(B.frozenRule (trainingBlockSeedEquiv e p).1 (trainingBlockSeedEquiv e p).2).reward
      ω.2.2 Finset.univ ω.1 ω.2.1+
    z*(B.frozenRule (trainingBlockSeedEquiv e p).1 (trainingBlockSeedEquiv e p).2).stoppingTime
      ω.2.2 Finset.univ ω.1 ω.2.1 ∂P.worldLaw (Measure.dirac ()))
  rw [hRule]

theorem Learner.empiricalTrainingBlock_expected_regret_le (ν : Measure Seed) [IsProbabilityMeasure ν]
    (e : Fin m ↪ Fin c) (Z : Reservoir n c × Seed → ℝ) (hZ : Measurable Z)
    {lo : ℝ} (hlo : 0<lo) (hlohi : lo≤1/4) (hRange : ∀ p, Z p∈Icc lo (1/4 : ℝ))
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hM : P.expectedMaximum≤1/80) :
    (∫ p, optimalScalarValue P 1 (Z p)-
      ((Learner.empiricalTrainingBlock ν e Z hZ).frozenRandomizedPolicy p.1 p.2).scalarObjective P 1 (Z p)
      ∂(P.reservoirLaw c).prod ν) ≤
      empiricalCapRegretConstant lo*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ) := by
  let η := (P.trainingRemainderLaw e).prod ν
  let T := trainingBlockScalar e Z
  have hT := measurable_trainingBlockScalar e hZ
  have hTRange (q) : T q∈Icc lo (1/4 : ℝ) := hRange ((trainingBlockSeedEquiv e).symm q)
  let B := Learner.empiricalCapAcceptance ((TrainingRemainderIndex n e → ℝ) × Seed) η T hT
  have hInt := B.integrable_selectedRegret P (P.integrable_maximum_of_bounded hcap) hT
    (fun q => hlo.le.trans (hTRange q).1) (Eventually.of_forall (fun q => (hTRange q).2))
  have hMP := P.trainingBlockSeedEquiv_measurePreserving e ν
  have hMean := hMP.hasLaw.integral_comp hInt.aestronglyMeasurable
  apply le_trans _ (Learner.empiricalCapAcceptance_expected_regret_le
    ((TrainingRemainderIndex n e → ℝ) × Seed) η T hT hlo hlohi hTRange P hcap hM)
  apply le_of_eq
  rw [← hMean]
  apply integral_congr_ae
  filter_upwards [] with p
  have hScalar : T (trainingBlockSeedEquiv e p)=Z p := by
    exact congrArg Z ((trainingBlockSeedEquiv e).symm_apply_apply p)
  change optimalScalarValue P 1 (Z p)-_ = optimalScalarValue P 1 (T (trainingBlockSeedEquiv e p))-
    (B.frozenRandomizedPolicy (trainingBlockSeedEquiv e p).1 (trainingBlockSeedEquiv e p).2).scalarObjective
      P 1 (T (trainingBlockSeedEquiv e p))
  rw [hScalar,Learner.empiricalTrainingBlock_frozen_scalar_eq ν e Z hZ η P p 1 (Z p)]

end ProphetSecretary.Model
