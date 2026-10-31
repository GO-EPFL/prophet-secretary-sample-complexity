import ProphetSecretary.Limiting.NormalizedDirectIndividualData
import ProphetSecretary.Limiting.CountableLikelihoodCrossCoefficients
import ProphetSecretary.Probability.NormalizedTargetScoreLimit

/-!
# The negative target coefficient of actual normalized individual arrays

The score is reversed explicitly. The raw reward, duration and maximum score
limits are combined with the fixed-base scaling identities. Critical scalar
stationarity identifies the limiting target coefficient with T'/w, which is
strictly negative for the chosen bounded-continuous duration direction.
-/

open MeasureTheory Set Filter BoundedContinuousFunction
open scoped Classical Topology NNReal BigOperators
namespace ProphetSecretary.Limiting.CountableInstance
open ProphetSecretary.Model ProphetSecretary.Probability

/-- This coefficient is total even on the discarded initial prefix; the final
experiment will retain only indices with positive, normalized base mean. -/
noncomputable def directIndividualNormalizedTargetScore (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ) (f : ℝ →ᵇ ℝ) (m : ℕ) : ℝ :=
  (B.directCanonicalPolicy hZero hw hc m).fixedBaseNormalizedTargetScore
    (B.directFiniteApproximation hZero m) (B.directIndividualArrayScore hZero i f m)

lemma directIndividualNormalizedTargetScore_eq (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (i : ℕ) (f : ℝ →ᵇ ℝ) (m : ℕ)
    (hM : 0<(B.directFiniteApproximation hZero m).expectedMaximum) :
    B.directIndividualNormalizedTargetScore hZero hw hc i f m=
      -((B.directFiniteApproximation hZero m).expectedMaximum⁻¹*
          ((B.directCanonicalPolicy hZero hw hc m).expectedRewardScore (B.directFiniteApproximation hZero m)
              (B.directIndividualArrayScore hZero i f m)-
            optimalCompetitiveRatio*(B.directFiniteApproximation hZero m).expectedMaximumScore
              (B.directIndividualArrayScore hZero i f m))-
        (B.directCanonicalPolicy hZero hw hc m).expectedDurationScore (B.directFiniteApproximation hZero m)
          (B.directIndividualArrayScore hZero i f m)) := by
  exact (B.directCanonicalPolicy hZero hw hc m).fixedBaseNormalizedTargetScore_eq
    (B.directFiniteApproximation hZero m) (B.directIndividualArrayScore hZero i f m)
    (B.directIndividualArrayScore_properties hZero i f m).1 hM

private lemma criticalIndividual_score_stationarity (B : CountableInstance) (hZero : B.terminal=0)
    {w c : ℝ} (hw : 0<w) (hc : 0<c) (hCritical : B.IsCritical w c) (i : ℕ) (f : ℝ →ᵇ ℝ) :
    w*(∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i : Measure ℝ) f (v.2.1 i)*
      (B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ()))+
    c*(∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i : Measure ℝ) f (v.2.1 i)*
      (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))=
      optimalCompetitiveRatio*w*B.prophetIndividualLikelihoodDerivative i (centeredBoundedScore (B.individuals i : Measure ℝ) f) := by
  let h := centeredBoundedScore (B.individuals i : Measure ℝ) f
  have hh := (continuous_centeredBoundedScore (B.individuals i : Measure ℝ) f).measurable
  have hb : ∀ᵐ x ∂(B.individuals i : Measure ℝ), |h x|≤1 :=
    Filter.Eventually.of_forall (centeredBoundedScore_abs_le_one (B.individuals i : Measure ℝ) f)
  have hm := centeredBoundedScore_mean (B.individuals i : Measure ℝ) f
  let π := B.valuePolicy hw hc
  have hR : π.scalarIndividualLikelihoodDerivative i 1 0 h=
      ∫ v : CompleteWorld Unit, h (v.2.1 i)*(B.valueRule w c).realizedReward 0 v
        ∂B.completeWorldLaw (Measure.dirac ()) := by
    unfold RandomizedCountablePolicy.scalarIndividualLikelihoodDerivative RandomizedCountablePolicy.scalarPayoff
    simp only [one_mul,zero_mul,add_zero]
    change (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedReward (B.terminal : ℝ) v*h (v.2.1 i)
      ∂B.completeWorldLaw (Measure.dirac ()))=_
    rw [hZero,NNReal.coe_zero]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)
  have hT : π.scalarIndividualLikelihoodDerivative i 0 1 h=
      ∫ v : CompleteWorld Unit, h (v.2.1 i)*(B.valueRule w c).realizedDuration v
        ∂B.completeWorldLaw (Measure.dirac ()) := by
    unfold RandomizedCountablePolicy.scalarIndividualLikelihoodDerivative RandomizedCountablePolicy.scalarPayoff
    simp only [zero_mul,one_mul,zero_add]
    change (∫ v : CompleteWorld Unit, (B.valueRule w c).realizedDuration v*h (v.2.1 i)
      ∂B.completeWorldLaw (Measure.dirac ()))=_
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun _ => mul_comm _ _)
  have hStat := B.critical_individual_likelihood_stationarity hw hc hCritical i h hh hb hm
  rw [π.scalarIndividualLikelihoodDerivative_weights i h hh hb w c,hR,hT] at hStat
  exact hStat

theorem directIndividualNormalizedTargetScore_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (hMean : B.expectedMaximum=1) {w c : ℝ} (hw : 0<w) (hc : 0<c) (hSum : w+c=1)
    (hCritical : B.IsCritical w c) (i : ℕ) (f : ℝ →ᵇ ℝ) :
    Tendsto (B.directIndividualNormalizedTargetScore hZero hw hc i f) atTop
      (𝓝 ((∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i : Measure ℝ) f (v.2.1 i)*
        (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ()))/w)) := by
  let dR := ∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i : Measure ℝ) f (v.2.1 i)*
    (B.valueRule w c).realizedReward 0 v ∂B.completeWorldLaw (Measure.dirac ())
  let dT := ∫ v : CompleteWorld Unit, centeredBoundedScore (B.individuals i : Measure ℝ) f (v.2.1 i)*
    (B.valueRule w c).realizedDuration v ∂B.completeWorldLaw (Measure.dirac ())
  let dM := B.prophetIndividualLikelihoodDerivative i (centeredBoundedScore (B.individuals i : Measure ℝ) f)
  have hRT := B.directScheduled_canonical_individual_score_limits hZero hw hc hSum i f
  have hMax := B.directIndividual_expectedMaximumScore_tendsto hZero i f
  have hMeanRaw := B.directFiniteApproximation_expectedMaximum_tendsto hZero
  have hMeanOne : Tendsto (fun m => (B.directFiniteApproximation hZero m).expectedMaximum) atTop (𝓝 (1 : ℝ)) := by
    simpa only [hMean] using hMeanRaw
  have hExpr := fixedBaseNormalizedTargetScore_tendsto
    (fun m => m+B.directVirtualCount hZero m) (B.directFiniteApproximation hZero)
    (B.directCanonicalPolicy hZero hw hc) (B.directIndividualArrayScore hZero i f)
    (fun m => (B.directIndividualArrayScore_properties hZero i f m).1) hMeanOne hRT.1 hRT.2 hMax
  have hCross : dR-dT-optimalCompetitiveRatio*dM= -dT/w :=
    normalized_stationarity_cross hw.ne' hSum (B.criticalIndividual_score_stationarity hZero hw hc hCritical i f)
  have hLimitEq : -(dR-dT-optimalCompetitiveRatio*dM)=dT/w := by rw [hCross,neg_div,neg_neg]
  rw [hLimitEq] at hExpr
  exact hExpr

end ProphetSecretary.Limiting.CountableInstance
