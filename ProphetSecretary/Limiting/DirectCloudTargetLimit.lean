import ProphetSecretary.Limiting.NormalizedDirectCloudData
import ProphetSecretary.Limiting.CountableLikelihoodCrossCoefficients
import ProphetSecretary.Probability.NormalizedTargetScoreLimit

/-!
# The reversed normalized cloud target coefficient at criticality

Raw complete reward, duration and maximum score limits pass through fixed-base
normalization. Critical scalar stationarity identifies the limiting reversed
target coefficient with T′/w. It is negative for a negative fixed-canonical
duration response; reoptimized duration is never differentiated.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

noncomputable def directCloudNormalizedTargetScore (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (b : ℝ) (m : ℕ) : ℝ :=
  (B.directCanonicalPolicy hZero hw hc m).fixedBaseNormalizedTargetScore
    (B.directFiniteApproximation hZero m) (B.directScheduledCloudScore hZero (Ioi b) m)

private lemma criticalCloud_score_stationarity (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c)
    (b : ℝ) (hb : (B.terminal:ℝ)<b) :
    w*(∫ v : CompleteWorld Unit, B.bandScore (Ioi b) v*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))+
    c*(∫ v : CompleteWorld Unit, B.bandScore (Ioi b) v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))=
      optimalCompetitiveRatio*w*B.prophetBandLikelihoodDerivative (Ioi b) := by
  let π := B.valuePolicy hw hc
  have hR : π.scalarBandLikelihoodDerivative (Ioi b) 1 0=
      ∫ v : CompleteWorld Unit, B.bandScore (Ioi b) v*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()) := by
    unfold RandomizedCountablePolicy.scalarBandLikelihoodDerivative RandomizedCountablePolicy.scalarPayoff
    simp only [one_mul,zero_mul,add_zero]
    change (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedReward (B.terminal:ℝ) v*B.bandScore (Ioi b) v
      ∂B.completeWorldLaw (Measure.dirac ()))=_
    rw [hZero,NNReal.coe_zero]
    exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_comm _ _))
  have hT : π.scalarBandLikelihoodDerivative (Ioi b) 0 1=
      ∫ v : CompleteWorld Unit, B.bandScore (Ioi b) v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()) := by
    unfold RandomizedCountablePolicy.scalarBandLikelihoodDerivative RandomizedCountablePolicy.scalarPayoff
    simp only [zero_mul,one_mul,zero_add]
    change (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*B.bandScore (Ioi b) v
      ∂B.completeWorldLaw (Measure.dirac ()))=_
    exact integral_congr_ae (Filter.Eventually.of_forall (fun _ => mul_comm _ _))
  have hStat := B.critical_band_likelihood_stationarity hw hc hCritical measurableSet_Ioi hb (Subset.refl (Ioi b))
  rw [π.scalarBandLikelihoodDerivative_weights measurableSet_Ioi hb (Subset.refl (Ioi b)) w c,hR,hT] at hStat
  exact hStat

theorem directCloudNormalizedTargetScore_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {w c : ℝ} (hw : 0<w) (hc : 0<c) (hNorm : w+c=1)
    (hCritical : B.IsCritical w c) (b : ℝ) (hb : (B.terminal:ℝ)<b) (hAtom : B.intensity {b}=0) :
    Tendsto (B.directCloudNormalizedTargetScore hZero hw hc b) atTop
      (𝓝 ((∫ v : CompleteWorld Unit, B.bandScore (Ioi b) v*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()))/w)) := by
  let dR := ∫ v : CompleteWorld Unit, B.bandScore (Ioi b) v*(B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ())
  let dT := ∫ v : CompleteWorld Unit, B.bandScore (Ioi b) v*(B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ())
  let dM := B.prophetBandLikelihoodDerivative (Ioi b)
  have hRT := B.directScheduled_canonical_cloud_score_limits hZero b hb hAtom hw hc hNorm
  have hMax := B.directScheduled_cloud_expectedMaximumScore_tendsto hZero measurableSet_Ioi hb (Subset.refl (Ioi b))
  have hMeanOne : Tendsto (fun m => (B.directFiniteApproximation hZero m).expectedMaximum) atTop (𝓝 (1:ℝ)) := by
    simpa only [hMean] using B.directFiniteApproximation_expectedMaximum_tendsto hZero
  have hS0 : (0:ℝ)∉Ioi b := not_lt.mpr (B.terminal.property.trans hb.le)
  have hExpr := fixedBaseNormalizedTargetScore_tendsto (fun m => m+B.directVirtualCount hZero m)
    (B.directFiniteApproximation hZero) (B.directCanonicalPolicy hZero hw hc) (B.directScheduledCloudScore hZero (Ioi b))
    (fun m => (B.directScheduledCloudScore_properties hZero measurableSet_Ioi hS0 m).1) hMeanOne hRT.1 hRT.2 hMax
  have hCross : dR-dT-optimalCompetitiveRatio*dM= -dT/w :=
    normalized_stationarity_cross hw.ne' hNorm (B.criticalCloud_score_stationarity hZero hw hc hCritical b hb)
  have hLimitEq : -(dR-dT-optimalCompetitiveRatio*dM)=dT/w := by rw [hCross,neg_div,neg_neg]
  rw [hLimitEq] at hExpr
  exact hExpr
end ProphetSecretary.Limiting.CountableInstance
