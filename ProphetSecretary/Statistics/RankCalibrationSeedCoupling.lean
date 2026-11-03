import ProphetSecretary.Statistics.RankCalibratedLearner
import ProphetSecretary.Probability.ValidationGridPermutation
import ProphetSecretary.Probability.DyadicMixtureCoin

/-!
# Coupling the validation permutations and mixture coin

The same independent key arrays generate the ideal and rounded validation
orders. The online coin is coupled independently of the entire offline
preparation. These are the two finite-grid changes after the clock-rounded
statistical analysis.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {TSeed PSeed : Type}

abbrev CalibrationKeyAux (n J : ℕ) (PSeed : Type) :=
  (Fin n → ℝ) × ((Fin n → ℝ) × PolicyQueryArray n J PSeed)

abbrev RankCalibrationCoupledSeed (n m J : ℕ) (TSeed PSeed : Type) :=
  (TargetGrid m → TSeed) × ((Fin m → CalibrationKeyAux n J PSeed) ×
    ((Fin n → ℝ) × (PolicyQueryArray n J PSeed × ℝ)))

variable [MeasurableSpace TSeed] [MeasurableSpace PSeed]

noncomputable def calibrationKeyAuxLaw (times : Measure (Fin n → ℝ)) (νP : Measure PSeed) :
    Measure (CalibrationKeyAux n J PSeed) :=
  (Instance.clocksLaw n).prod (times.prod (policyQueryArrayLaw νP))

instance calibrationKeyAuxLaw_probability (times : Measure (Fin n → ℝ)) (νP : Measure PSeed)
    [IsProbabilityMeasure times] [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (calibrationKeyAuxLaw (J := J) times νP) := by
  unfold calibrationKeyAuxLaw
  infer_instance

noncomputable def rankCalibrationCoupledSeedLaw (νT : Measure TSeed) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) : Measure (RankCalibrationCoupledSeed n m J TSeed PSeed) :=
  (targetQueryArrayLaw νT).prod ((Measure.pi (fun _ => calibrationKeyAuxLaw times νP)).prod
    (times.prod ((policyQueryArrayLaw νP).prod Instance.uniformClock)))

instance rankCalibrationCoupledSeedLaw_probability (νT : Measure TSeed) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times] [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (rankCalibrationCoupledSeedLaw (m := m) (J := J) νT νP times) := by
  unfold rankCalibrationCoupledSeedLaw
  infer_instance

def projectRankCalibrationSeed (order : (Fin n → ℝ) → Equiv.Perm (Fin n)) (coin : ℝ → ℝ)
    (s : RankCalibrationCoupledSeed n m J TSeed PSeed) : RankCalibratedSeed n m J TSeed PSeed :=
  (s.1,(fun j => (order (s.2.1 j).1,(s.2.1 j).2)),s.2.2.1,s.2.2.2.1,coin s.2.2.2.2)

lemma projectRankCalibrationSeed_measurePreserving (νT : Measure TSeed) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times] [IsProbabilityMeasure νT] [IsProbabilityMeasure νP]
    {order : (Fin n → ℝ) → Equiv.Perm (Fin n)} (hOrder : Measurable order)
    {coin : ℝ → ℝ} (hCoin : Measurable coin) :
    MeasurePreserving (projectRankCalibrationSeed (m := m) (J := J) order coin)
      (rankCalibrationCoupledSeedLaw νT νP times)
      (rankCalibratedSeedLaw νT νP ((Instance.clocksLaw n).map order) times
        (Instance.uniformClock.map coin)) := by
  let ord := (Instance.clocksLaw n).map order
  let c := Instance.uniformClock.map coin
  haveI : IsProbabilityMeasure ord := Measure.isProbabilityMeasure_map hOrder.aemeasurable
  haveI : IsProbabilityMeasure c := Measure.isProbabilityMeasure_map hCoin.aemeasurable
  have hp : MeasurePreserving order (Instance.clocksLaw n) ord := ⟨hOrder,rfl⟩
  have hc : MeasurePreserving coin Instance.uniformClock c := ⟨hCoin,rfl⟩
  let A := policyQueryArrayLaw (n := n) (J := J) νP
  have hv := measurePreserving_pi (fun _ : Fin m => calibrationKeyAuxLaw (J := J) times νP)
    (fun _ : Fin m => rankValidationAuxLaw (J := J) ord times νP)
      (fun _ => hp.prod (MeasurePreserving.id (times.prod A)))
  exact (MeasurePreserving.id (targetQueryArrayLaw (m := m) νT)).prod
    (hv.prod ((MeasurePreserving.id times).prod ((MeasurePreserving.id A).prod hc)))

lemma coupledValidationKeys_measurePreserving (νT : Measure TSeed) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times] [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    MeasurePreserving (fun s : RankCalibrationCoupledSeed n m J TSeed PSeed => fun j => (s.2.1 j).1)
      (rankCalibrationCoupledSeedLaw νT νP times)
      (Measure.pi (fun _ : Fin m => Instance.clocksLaw n)) := by
  let A := targetQueryArrayLaw (m := m) νT
  let V := Measure.pi (fun _ : Fin m => calibrationKeyAuxLaw (J := J) times νP)
  let R := times.prod ((policyQueryArrayLaw (n := n) (J := J) νP).prod Instance.uniformClock)
  have h := measurePreserving_pi (fun _ : Fin m => calibrationKeyAuxLaw (J := J) times νP)
    (fun _ : Fin m => Instance.clocksLaw n) (fun _ => measurePreserving_fst)
  exact h.comp ((measurePreserving_fst (μ := V) (ν := R)).comp
    (measurePreserving_snd (μ := A) (ν := V.prod R)))

abbrev CoupledCalibrationOffline (n m J : ℕ) (TSeed PSeed : Type) :=
  Reservoir n (2*m) × ((TargetGrid m → TSeed) × (Fin m → CalibrationKeyAux n J PSeed))

noncomputable def coupledCalibrationOfflineLaw (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) : Measure (CoupledCalibrationOffline n m J TSeed PSeed) :=
  (P.reservoirLaw (2*m)).prod ((targetQueryArrayLaw νT).prod
    (Measure.pi (fun _ => calibrationKeyAuxLaw times νP)))

instance coupledCalibrationOfflineLaw_probability (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times] [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (coupledCalibrationOfflineLaw (m := m) (J := J) P νT νP times) := by
  unfold coupledCalibrationOfflineLaw
  infer_instance

def coupledCalibrationOfflineCoin (p : Reservoir n (2*m) × RankCalibrationCoupledSeed n m J TSeed PSeed) :
    CoupledCalibrationOffline n m J TSeed PSeed × ℝ :=
  ((p.1,p.2.1,p.2.2.1),p.2.2.2.2.2)

lemma coupledCalibrationOfflineCoin_measurePreserving (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    (times : Measure (Fin n → ℝ)) [IsProbabilityMeasure times] [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    MeasurePreserving (coupledCalibrationOfflineCoin (m := m) (J := J))
      ((P.reservoirLaw (2*m)).prod (rankCalibrationCoupledSeedLaw νT νP times))
      ((coupledCalibrationOfflineLaw P νT νP times).prod Instance.uniformClock) := by
  let Y := P.reservoirLaw (2*m)
  let T := targetQueryArrayLaw (m := m) νT
  let V := Measure.pi (fun _ : Fin m => calibrationKeyAuxLaw (J := J) times νP)
  let A := policyQueryArrayLaw (n := n) (J := J) νP
  let C := Instance.uniformClock
  let R := times.prod (A.prod C)
  have h1 := (MeasurePreserving.id Y).prod ((measurePreserving_prodAssoc T V R).symm MeasurableEquiv.prodAssoc)
  have h2 := (measurePreserving_prodAssoc Y (T.prod V) R).symm MeasurableEquiv.prodAssoc
  have h3 := (measurePreserving_snd (μ := A) (ν := C)).comp
    (measurePreserving_snd (μ := times) (ν := A.prod C))
  exact ((MeasurePreserving.id (Y.prod (T.prod V))).prod h3).comp (h2.comp h1)

end ProphetSecretary.Statistics.Calibration
