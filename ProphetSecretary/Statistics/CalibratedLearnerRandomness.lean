import ProphetSecretary.Statistics.CalibratedTrainingBlocks
import ProphetSecretary.Statistics.CalibrationNumericalTarget
import ProphetSecretary.Probability.ProductRegrouping

/-!
# Independent randomness of the two-block calibrated learner

Target-query seeds, validation clocks and query arrays, and the fresh online
query array and mixture coin are separate finite product factors. Combining
the literal second training block with its independent auxiliary arrays gives
actual iid validation worlds. This proves the independence used by calibration.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {TSeed PSeed : Type*} [MeasurableSpace TSeed] [MeasurableSpace PSeed]

abbrev PolicyQueryArray (n J : ℕ) (PSeed : Type*) := (Fin n × Fin (J+1)) → PSeed
abbrev ValidationAux (n m J : ℕ) (PSeed : Type*) :=
  Fin m → ((Fin n → ℝ) × PolicyQueryArray n J PSeed)
abbrev CalibratedSeed (n m J : ℕ) (TSeed PSeed : Type*) :=
  (TargetGrid m → TSeed) × (ValidationAux n m J PSeed × (PolicyQueryArray n J PSeed × ℝ))

noncomputable def policyQueryArrayLaw (νP : Measure PSeed) : Measure (PolicyQueryArray n J PSeed) :=
  Measure.pi (fun _ => νP)

instance policyQueryArrayLaw_probability (νP : Measure PSeed) [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (policyQueryArrayLaw (n := n) (J := J) νP) := by
  unfold policyQueryArrayLaw
  infer_instance

noncomputable def targetQueryArrayLaw (νT : Measure TSeed) : Measure (TargetGrid m → TSeed) :=
  Measure.pi (fun _ => νT)

instance targetQueryArrayLaw_probability (νT : Measure TSeed) [IsProbabilityMeasure νT] :
    IsProbabilityMeasure (targetQueryArrayLaw (m := m) νT) := by
  unfold targetQueryArrayLaw
  infer_instance

noncomputable def validationAuxLaw (νP : Measure PSeed) : Measure (ValidationAux n m J PSeed) :=
  Measure.pi (fun _ => (Instance.clocksLaw n).prod (policyQueryArrayLaw (J := J) νP))

instance validationAuxLaw_probability (νP : Measure PSeed) [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (validationAuxLaw (n := n) (m := m) (J := J) νP) := by
  unfold validationAuxLaw
  infer_instance

noncomputable def calibratedSeedLaw (νT : Measure TSeed) (νP : Measure PSeed) :
    Measure (CalibratedSeed n m J TSeed PSeed) :=
  (targetQueryArrayLaw νT).prod ((validationAuxLaw νP).prod
    ((policyQueryArrayLaw νP).prod Instance.uniformClock))

instance calibratedSeedLaw_probability (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (calibratedSeedLaw (n := n) (m := m) (J := J) νT νP) := by
  unfold calibratedSeedLaw
  infer_instance

/-- Each profile combines a second-block offer vector with its own clocks and query seeds. -/
def validationWorlds (v : Fin m → (Fin n → ℝ)) (a : ValidationAux n m J PSeed) :
    Fin m → World n (PolicyQueryArray n J PSeed) := fun j => (v j, a j)

lemma validationWorlds_measurePreserving (P : Instance n) (νP : Measure PSeed)
    [IsProbabilityMeasure νP] :
    MeasurePreserving (fun p => validationWorlds p.1 p.2)
      ((Measure.pi (fun _ : Fin m => P.valuesLaw)).prod (validationAuxLaw (J := J) νP))
      (Measure.pi (fun _ : Fin m => P.worldLaw (policyQueryArrayLaw (J := J) νP))) := by
  exact (measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ)
    ((Fin n → ℝ) × PolicyQueryArray n J PSeed) (Fin m)
    (fun _ => P.valuesLaw) (fun _ => (Instance.clocksLaw n).prod (policyQueryArrayLaw νP))).symm
      (MeasurableEquiv.arrowProdEquivProdArrow _ _ _)

/-- The exact decomposition of all training and auxiliary randomness used before online arrivals. -/
def calibratedExperiment (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) :
    (((Fin n × Fin m) → ℝ) × (TargetGrid m → TSeed)) ×
      ((Fin m → World n (PolicyQueryArray n J PSeed)) × (PolicyQueryArray n J PSeed × ℝ)) :=
  let data := trainingAndValidation p.1
  ((data.1,p.2.1),(validationWorlds data.2 p.2.2.1,p.2.2.2))

/-- First-block information, iid validation worlds, and online seeds/coin have independent product law. -/
lemma calibratedExperiment_measurePreserving (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    MeasurePreserving (calibratedExperiment (n := n) (m := m) (J := J))
      ((P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP))
      (((P.trainingCoordinateLaw m).prod (targetQueryArrayLaw νT)).prod
        ((Measure.pi (fun _ : Fin m => P.worldLaw (policyQueryArrayLaw (J := J) νP))).prod
          ((policyQueryArrayLaw (n := n) (J := J) νP).prod Instance.uniformClock))) := by
  let A := P.trainingCoordinateLaw m
  let B := Measure.pi (fun _ : Fin m => P.valuesLaw)
  let C := targetQueryArrayLaw (m := m) νT
  let D := validationAuxLaw (n := n) (m := m) (J := J) νP
  let E := (policyQueryArrayLaw (n := n) (J := J) νP).prod Instance.uniformClock
  have hData := (trainingAndValidation_measurePreserving (m := m) P).prod
    (MeasurePreserving.id (calibratedSeedLaw (n := n) (m := m) (J := J) νT νP))
  have hShuffle := productPairShuffle_measurePreserving A B C (D.prod E)
  have hAssoc := (MeasurePreserving.id (A.prod C)).prod
    ((measurePreserving_prodAssoc B D E).symm MeasurableEquiv.prodAssoc)
  have hJoin := (MeasurePreserving.id (A.prod C)).prod
    ((validationWorlds_measurePreserving (m := m) (J := J) P νP).prod (MeasurePreserving.id E))
  exact hJoin.comp (hAssoc.comp (hShuffle.comp hData))

end ProphetSecretary.Statistics.Calibration
