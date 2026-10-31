import ProphetSecretary.Limiting.HybridObserverPayoff

/-!
# Exact score-weighted payoff transport for a truncated callback

The same measurable analytical function of the complete finite observer
multiplies reward or duration in both executions. Its values are not supplied
to the online callback. Both expectations use the actual observer product law.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Limiting
open CountableInstance
variable {N : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem HybridRule.integral_scoredPayoffs_eq_extended
    (π : HybridRule N Seed) (hπ : π.IsMeasurable) (B : CountableInstance)
    (ν : Measure Seed) [IsProbabilityMeasure ν] {b : ℝ} (hb : (B.terminal:ℝ)<b)
    (G : FiniteObserverWorld N Seed → ℝ) (hG : Measurable G) :
    ((∫ v, G (hybridObserverWorld v)*π.realizedReward B.terminal v
      ∂(B.truncation N b hb).law ν)=
      ∫ v, G (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v)*
        (extendTruncatedRule π b).realizedReward B.terminal v ∂B.completeWorldLaw ν) ∧
    ((∫ v, G (hybridObserverWorld v)*π.realizedDuration v
      ∂(B.truncation N b hb).law ν)=
      ∫ v, G (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v)*
        (extendTruncatedRule π b).realizedDuration v ∂B.completeWorldLaw ν) := by
  let FR := fun q => G q*π.observableReward B.terminal q
  let FT := fun q => G q*π.observableDuration q
  have hFR : Measurable FR := hG.mul (π.measurable_observableReward hπ B.terminal)
  have hFT : Measurable FT := hG.mul (π.measurable_observableDuration hπ)
  have hHybrid := hybrid_finiteObserver_measurePreserving (B.individualPrefix N) (B.intensityAbove b hb) ν
  have hFull := B.finiteObserverProjection_measurePreserving ν N hb
  have hRMap : (∫ v, FR (hybridObserverWorld v) ∂(B.truncation N b hb).law ν)=
      ∫ v, FR (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v) ∂B.completeWorldLaw ν :=
    (hHybrid.hasLaw.integral_comp hFR.aestronglyMeasurable).trans (hFull.hasLaw.integral_comp hFR.aestronglyMeasurable).symm
  have hTMap : (∫ v, FT (hybridObserverWorld v) ∂(B.truncation N b hb).law ν)=
      ∫ v, FT (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v) ∂B.completeWorldLaw ν :=
    (hHybrid.hasLaw.integral_comp hFT.aestronglyMeasurable).trans (hFull.hasLaw.integral_comp hFT.aestronglyMeasurable).symm
  have hHP := π.hybrid_payoffs_eq_observable hπ (B.truncation N b hb) ν
  have hFP := π.extended_payoffs_eq_observable hπ B ν hb
  constructor
  · exact (integral_congr_ae (hHP.mono (fun v hv =>
      congrArg (fun x => G (hybridObserverWorld v)*x) hv.2.symm))).trans (hRMap.trans
        (integral_congr_ae (hFP.mono (fun v hv =>
          congrArg (fun x => G (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v)*x) hv.2))))
  · exact (integral_congr_ae (hHP.mono (fun v hv =>
      congrArg (fun x => G (hybridObserverWorld v)*x) hv.1.symm))).trans (hTMap.trans
        (integral_congr_ae (hFP.mono (fun v hv =>
          congrArg (fun x => G (truncatedObserverWorld (finiteCutoffCountingMeasure b v.1) v)*x) hv.1))))
end ProphetSecretary.Limiting
