import ProphetSecretary.Limiting.TruncatedScorePayoffTransport
import ProphetSecretary.Limiting.CountableBandScore

/-!
# Exact complete cloud-score transport through a positive truncation

An upper band above the retained cutoff has the same complete count in the
full counting measure and its truncated observer. This count includes future
points and appears only as an analytical multiplier in the expectation.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance
variable {N : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem HybridRule.integral_bandScorePayoffs_eq_extended
    (π : HybridRule N Seed) (hπ : π.IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {d : ℝ} (hd : (B.terminal:ℝ)<d)
    (b : ℝ) (hdb : d≤b) :
    ((∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*π.realizedReward B.terminal v
      ∂(B.truncation N d hd).law ν)=
      ∫ v, B.bandScore (Ioi b) v*(extendTruncatedRule π d).realizedReward B.terminal v ∂B.completeWorldLaw ν) ∧
    ((∫ v, ((pointCount (univ ×ˢ Ioi b) v.1:ℝ)-B.intensity.real (Ioi b))*π.realizedDuration v
      ∂(B.truncation N d hd).law ν)=
      ∫ v, B.bandScore (Ioi b) v*(extendTruncatedRule π d).realizedDuration v ∂B.completeWorldLaw ν) := by
  let S : Set Point := univ ×ˢ Ioi b
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Ioi
  have hSub : S⊆univ ×ˢ Ioi d := fun _ hp => ⟨hp.1,hdb.trans_lt hp.2⟩
  let G : FiniteObserverWorld N Seed → ℝ := fun q => (q.1:Measure Point).real S-B.intensity.real (Ioi b)
  have hG : Measurable G := (((Measure.measurable_coe hS).ennreal_toReal).comp
    (measurable_subtype_coe.comp measurable_fst)).sub_const _
  have hHybrid (v : HybridWorld N Seed) : G (hybridObserverWorld v)=
      (pointCount S v.1:ℝ)-B.intensity.real (Ioi b) := by
    change (configurationFiniteMeasure v.1:Measure Point).real S-_= _
    rw [configurationFiniteMeasure_coe,Measure.real,countingMeasure_eq_pointCount hS,ENNReal.toReal_natCast]
  have hFull : ∀ᵐ v ∂B.completeWorldLaw ν,
      G (truncatedObserverWorld (N := N) (finiteCutoffCountingMeasure d v.1) v)=B.bandScore (Ioi b) v := by
    have hMP : MeasurePreserving (Prod.fst : CompleteWorld Seed → BandConfigurations)
      (B.completeWorldLaw ν) B.bandConfigurationsLaw := measurePreserving_fst
    filter_upwards [hMP.quasiMeasurePreserving.ae (B.finiteCutoffCountingMeasure_coe_ae hd),
      hMP.quasiMeasurePreserving.ae (B.bandCountingMeasure_eq_natCount_ae hd hS hSub)] with v hCut hCount
    change (finiteCutoffCountingMeasure d v.1:Measure Point).real S-B.intensity.real (Ioi b)=_
    rw [B.bandScore_eq]
    change (finiteCutoffCountingMeasure d v.1:Measure Point).real S-B.intensity.real (Ioi b)=
      (bandPointCount S v.1:ℝ)-B.intensity.real (Ioi b)
    rw [Measure.real,hCut,Measure.restrict_apply hS,inter_eq_left.mpr hSub,hCount,ENNReal.toReal_natCast]
  have h := π.integral_scoredPayoffs_eq_extended hπ B ν hd G hG
  constructor
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun v =>
      congrArg (fun x => x*π.realizedReward B.terminal v) (hHybrid v).symm))).trans
      (h.1.trans (integral_congr_ae (hFull.mono (fun v hv =>
        congrArg (fun x => x*(extendTruncatedRule π d).realizedReward B.terminal v) hv))))
  · exact (integral_congr_ae (Filter.Eventually.of_forall (fun v =>
      congrArg (fun x => x*π.realizedDuration v) (hHybrid v).symm))).trans
      (h.2.trans (integral_congr_ae (hFull.mono (fun v hv =>
        congrArg (fun x => x*(extendTruncatedRule π d).realizedDuration v) hv))))
end ProphetSecretary.Limiting
