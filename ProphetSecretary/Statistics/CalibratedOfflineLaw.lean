import ProphetSecretary.Statistics.CalibratedPreparedPolicy

/-!
# Conditioning on offline data

The actual training transcript splits into the first-block information and
validation worlds. The query array and the one mixing coin for the online
run are independent of both. The product representations here are used
only to integrate the causal execution.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type}

abbrev OfflineData (n m J : ℕ) (TSeed PSeed : Type) :=
  FirstInformation n m TSeed × ValidationWorldArray n m J PSeed

abbrev OnlineCalibrationSeed (n J : ℕ) (PSeed : Type) := PolicyQueryArray n J PSeed × ℝ

variable [MeasurableSpace TSeed] [MeasurableSpace PSeed]

noncomputable def offlineDataLaw (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed) :
    Measure (OfflineData n m J TSeed PSeed) :=
  (firstInformationLaw P νT).prod (validationWorldArrayLaw P νP)

instance offlineDataLaw_probability (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (offlineDataLaw (m := m) (J := J) P νT νP) := by
  unfold offlineDataLaw
  infer_instance

noncomputable def onlineCalibrationSeedLaw (νP : Measure PSeed) : Measure (OnlineCalibrationSeed n J PSeed) :=
  (policyQueryArrayLaw νP).prod Instance.uniformClock

instance onlineCalibrationSeedLaw_probability (νP : Measure PSeed) [IsProbabilityMeasure νP] :
    IsProbabilityMeasure (onlineCalibrationSeedLaw (n := n) (J := J) νP) := by
  unfold onlineCalibrationSeedLaw
  infer_instance

def splitOfflineOnline (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) :
    OfflineData n m J TSeed PSeed × OnlineCalibrationSeed n J PSeed :=
  (calibratedOfflineData p,p.2.2.2)

lemma splitOfflineOnline_measurePreserving (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    MeasurePreserving (splitOfflineOnline (m := m) (J := J))
      ((P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP))
      ((offlineDataLaw P νT νP).prod (onlineCalibrationSeedLaw νP)) := by
  exact (measurePreserving_prodAssoc (firstInformationLaw (m := m) P νT)
    (validationWorldArrayLaw (m := m) (J := J) P νP) (onlineCalibrationSeedLaw (n := n) (J := J) νP)).symm
      MeasurableEquiv.prodAssoc |>.comp (calibratedExperiment_measurePreserving (m := m) (J := J) P νT νP)

def offlineEmpiricalBlock (d : OfflineData n m J TSeed PSeed) : Reservoir n m :=
  reservoirCoordinates.symm d.1.1

noncomputable def offlineTarget [NeZero m] (mu : ℝ) (targetEstimate : TargetEstimator n m TSeed)
    (d : OfflineData n m J TSeed PSeed) : ℝ :=
  computedTarget mu targetEstimate d.1.1 d.1.2

noncomputable def offlinePrepare [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : OfflineData n m J TSeed PSeed) : PreparedCalibration n m :=
  (offlineEmpiricalBlock d,validationSelection zlo zhi policyEstimate (offlineEmpiricalBlock d) d.2
    (offlineTarget mu targetEstimate d))

lemma measurable_offlineEmpiricalBlock :
    Measurable (offlineEmpiricalBlock (n := n) (m := m) (J := J) (TSeed := TSeed) (PSeed := PSeed)) :=
  reservoirCoordinates.symm.measurable.comp (measurable_fst.comp measurable_fst)

lemma measurable_offlineTarget [NeZero m] (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (he : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => estimate p.1 p.2.1 p.2.2)) :
    Measurable (offlineTarget (J := J) (PSeed := PSeed) mu estimate) :=
  (measurable_computedTarget mu estimate he).comp measurable_fst

lemma measurable_offlinePrepare [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (hT : Measurable (fun p : Reservoir n m × (ℝ × TSeed) => targetEstimate p.1 p.2.1 p.2.2))
    (hC : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      policyEstimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    Measurable (offlinePrepare (J := J) mu zlo zhi targetEstimate policyEstimate) :=
  measurable_offlineEmpiricalBlock.prodMk (measurable_validationSelection zlo zhi policyEstimate hC
    measurable_offlineEmpiricalBlock measurable_snd (measurable_offlineTarget mu targetEstimate hT))

omit [MeasurableSpace TSeed] [MeasurableSpace PSeed] in
lemma offlinePrepare_eq_prepare [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) :
    offlinePrepare mu zlo zhi targetEstimate policyEstimate (calibratedOfflineData p) =
      prepare mu zlo zhi targetEstimate policyEstimate p := rfl

omit [MeasurableSpace TSeed] [MeasurableSpace PSeed] in
lemma offlinePrepare_bounds [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (d : OfflineData n m J TSeed PSeed) :
    1≤(offlinePrepare mu zlo zhi targetEstimate policyEstimate d).2.1 ∧
    (offlinePrepare mu zlo zhi targetEstimate policyEstimate d).2.1≤J+2 ∧
    (offlinePrepare mu zlo zhi targetEstimate policyEstimate d).2.2∈Ioc (0 : ℝ) 1 := by
  have hρ := computedTarget_range mu targetEstimate d.1.1 d.1.2
  exact validationSelection_bounds zlo zhi policyEstimate (offlineEmpiricalBlock d)
    d.2 ⟨(by norm_num : (0 : ℝ)<1/2).trans_le hρ.1,hρ.2.trans (by norm_num)⟩

/-- Move offline data to the outer factor of the actual learner world. -/
def splitCalibratedWorld (ω : World n (Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed)) :
    OfflineData n m J TSeed PSeed × World n (OnlineCalibrationSeed n J PSeed) :=
  (calibratedOfflineData ω.2.2,(ω.1,ω.2.1,ω.2.2.2.2.2))

lemma splitCalibratedWorld_measurePreserving (P : Instance n) (νT : Measure TSeed) (νP : Measure PSeed)
    [IsProbabilityMeasure νT] [IsProbabilityMeasure νP] :
    MeasurePreserving (splitCalibratedWorld (m := m) (J := J))
      (P.worldLaw ((P.reservoirLaw (2*m)).prod (calibratedSeedLaw νT νP)))
      ((offlineDataLaw P νT νP).prod (P.worldLaw (onlineCalibrationSeedLaw νP))) := by
  let X := P.valuesLaw
  let U := Instance.clocksLaw n
  let D := (P.reservoirLaw (2*m)).prod (calibratedSeedLaw (n := n) (m := m) (J := J) νT νP)
  let O := offlineDataLaw (m := m) (J := J) P νT νP
  let R := onlineCalibrationSeedLaw (n := n) (J := J) νP
  have h1 := (measurePreserving_prodAssoc X U D).symm MeasurableEquiv.prodAssoc
  have h2 := (MeasurePreserving.id (X.prod U)).prod (splitOfflineOnline_measurePreserving (m := m) (J := J) P νT νP)
  have h3 := (measurePreserving_prodAssoc (X.prod U) O R).symm MeasurableEquiv.prodAssoc
  have h4 := (Measure.measurePreserving_swap (μ := X.prod U) (ν := O)).prod (MeasurePreserving.id R)
  have h5 := measurePreserving_prodAssoc O (X.prod U) R
  have h6 := (MeasurePreserving.id O).prod (measurePreserving_prodAssoc X U R)
  exact h6.comp (h5.comp (h4.comp (h3.comp (h2.comp h1))))

end ProphetSecretary.Statistics.Calibration
