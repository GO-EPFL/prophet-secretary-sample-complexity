import ProphetSecretary.Statistics.RankCalibrationSeedCoupling

/-!
# Finite-bit seeds of the rank calibration

The validation keys, validation clocks, online clocks, and mixture coin
are separate independent finite arrays. Sorting and interpreting these
bits realize exactly the laws used by the rounded rank learner.
-/

open MeasureTheory

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ} {TSeed PSeed : Type}

abbrev RankCalibrationClockBits (n b : ℕ) := Fin n → Fin b → Bool

abbrev RankCalibrationValidationBits (n J b : ℕ) (PSeed : Type) :=
  RankCalibrationClockBits n b × (RankCalibrationClockBits n b × PolicyQueryArray n J PSeed)

abbrev RankCalibrationBits (n m J b c : ℕ) (TSeed PSeed : Type) :=
  (TargetGrid m → TSeed) × ((Fin m → RankCalibrationValidationBits n J b PSeed) ×
    (RankCalibrationClockBits n b × (PolicyQueryArray n J PSeed × (Fin c → Bool))))

noncomputable def rankCalibrationClockBitsLaw (n b : ℕ) : Measure (RankCalibrationClockBits n b) :=
  Measure.pi (fun _ => fairBitVectorLaw b)

instance rankCalibrationClockBitsLaw_probability (n b : ℕ) :
    IsProbabilityMeasure (rankCalibrationClockBitsLaw n b) := by
  unfold rankCalibrationClockBitsLaw
  infer_instance

def interpretRankValidationBits (b : ℕ) (p : RankCalibrationValidationBits n J b PSeed) :
    RankValidationAux n J PSeed :=
  ((countedDyadicValidationPermutation b p.1).1,
    (fun i => (((countedDyadicSortedClocks b p.2.1).1 i : ℚ):ℝ)),p.2.2)

def interpretRankCalibrationBits (b c : ℕ) (p : RankCalibrationBits n m J b c TSeed PSeed) :
    RankCalibratedSeed n m J TSeed PSeed :=
  (p.1,fun j => interpretRankValidationBits b (p.2.1 j),
    (fun i => (((countedDyadicSortedClocks b p.2.2.1).1 i : ℚ):ℝ)),
      p.2.2.2.1,((countedDyadicUniform c p.2.2.2.2).1 : ℝ))

variable [MeasurableSpace TSeed] [MeasurableSpace PSeed]

noncomputable def rankCalibrationValidationBitsLaw (b : ℕ) (νP : Measure PSeed) :
    Measure (RankCalibrationValidationBits n J b PSeed) :=
  (rankCalibrationClockBitsLaw n b).prod ((rankCalibrationClockBitsLaw n b).prod (policyQueryArrayLaw νP))

instance rankCalibrationValidationBitsLaw_probability (b : ℕ) (νP : Measure PSeed) [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (rankCalibrationValidationBitsLaw (n := n) (J := J) b νP) := by
  unfold rankCalibrationValidationBitsLaw
  infer_instance

noncomputable def rankCalibrationBitsLaw (b c : ℕ) (νT : Measure TSeed) (νP : Measure PSeed) :
    Measure (RankCalibrationBits n m J b c TSeed PSeed) :=
  (targetQueryArrayLaw νT).prod ((Measure.pi (fun _ => rankCalibrationValidationBitsLaw b νP)).prod
    ((rankCalibrationClockBitsLaw n b).prod ((policyQueryArrayLaw νP).prod (fairBitVectorLaw c))))

instance rankCalibrationBitsLaw_probability (b c : ℕ) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (rankCalibrationBitsLaw (n := n) (m := m) (J := J) b c νT νP) := by
  unfold rankCalibrationBitsLaw
  infer_instance

theorem interpretRankCalibrationBits_measurePreserving (b c : ℕ)
    (νT : Measure TSeed) (νP : Measure PSeed) [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    MeasurePreserving (interpretRankCalibrationBits (n := n) (m := m) (J := J) b c)
      (rankCalibrationBitsLaw b c νT νP)
      (rankCalibratedSeedLaw νT νP
        ((Instance.clocksLaw n).map (roundedValidationPermutation (N := 2^b) (by positivity)))
        (roundedSortedTimesLaw n (2^b) (by positivity))
        (Instance.uniformClock.map (uniformGridRound (2^c) (by positivity)))) := by
  let K := (Instance.clocksLaw n).map (roundedValidationPermutation (N := 2^b) (by positivity))
  let S := roundedSortedTimesLaw n (2^b) (by positivity)
  let A := policyQueryArrayLaw (n := n) (J := J) νP
  let C := Instance.uniformClock.map (uniformGridRound (2^c) (by positivity))
  have hK : MeasurePreserving (fun p : RankCalibrationClockBits n b => (countedDyadicValidationPermutation b p).1)
      (rankCalibrationClockBitsLaw n b) K := ⟨measurable_of_countable _,map_countedDyadicValidationPermutation n b⟩
  have hS : MeasurePreserving (fun p : RankCalibrationClockBits n b => fun i =>
      (((countedDyadicSortedClocks b p).1 i : ℚ):ℝ)) (rankCalibrationClockBitsLaw n b) S :=
    ⟨measurable_of_countable _,map_countedDyadicSortedClocks n b⟩
  have hC : MeasurePreserving (fun p : Fin c → Bool => ((countedDyadicUniform c p).1 : ℝ))
      (fairBitVectorLaw c) C := ⟨measurable_of_countable _,map_countedDyadicUniform c⟩
  haveI : IsProbabilityMeasure K := by
    rw [← hK.map_eq]
    exact Measure.isProbabilityMeasure_map hK.measurable.aemeasurable
  haveI : IsProbabilityMeasure S := by
    rw [← hS.map_eq]
    exact Measure.isProbabilityMeasure_map hS.measurable.aemeasurable
  haveI : IsProbabilityMeasure C := by
    rw [← hC.map_eq]
    exact Measure.isProbabilityMeasure_map hC.measurable.aemeasurable
  have hV := measurePreserving_pi
    (fun _ : Fin m => rankCalibrationValidationBitsLaw (n := n) (J := J) b νP)
    (fun _ : Fin m => rankValidationAuxLaw (J := J) K S νP)
      (fun _ => hK.prod (hS.prod (MeasurePreserving.id A)))
  exact (MeasurePreserving.id (targetQueryArrayLaw (m := m) νT)).prod
    (hV.prod (hS.prod ((MeasurePreserving.id A).prod hC)))

end ProphetSecretary.Statistics.Calibration
