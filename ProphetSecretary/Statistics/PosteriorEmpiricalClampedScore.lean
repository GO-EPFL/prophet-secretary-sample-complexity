import ProphetSecretary.Statistics.PosteriorEmpiricalRegret
import ProphetSecretary.Model.FrozenSelectedGapIntegrability

/-!
# Integrating the proved small-mean clamp for the actual empirical learner

A single interval endpoint is used for the callback and the clamp.
The pointwise clamp is the one supplied by `bounded_smallMean_clamp`;
selected-weight regret is controlled by the actual independent block.
All three integrands are proved integrable before their expectations are
compared. Paper correspondence: `eq:bayes-clamped-score` and
`eq:bayes-empirical-loss`.
-/

open MeasureTheory Set Filter
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n m N : ℕ} [NeZero m]

theorem posteriorEmpirical_frozen_score_lower (F : FinitePrior n) (N b k : ℕ)
    (h : b+2*m≤trainingLength N b k) {beta : ℝ} (hBeta : beta∈Ioo (4/5 : ℝ) 1)
    (P : Instance n) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (hSmall : P.expectedMaximum≤1/80)
    (hClamp : ∀ (π : RandomizedPolicy n) (lam r : ℝ), lam∈Icc (0 : ℝ) 1 →
      π.normalizedRegret P (max (4/5) (min beta lam))≤r →
      normalizedScalarGap P lam/40-5*r≤π.scalarObjective P lam (1-lam)-
        optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam)) :
    (∫ p : Reservoir n (trainingLength N b k) × Unit,
      normalizedScalarGap P (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))
      ∂(P.reservoirLaw (trainingLength N b k)).prod (Measure.dirac ()))/40-
        5*(empiricalCapRegretConstant (1-beta)*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ)) ≤
    ∫ p : Reservoir n (trainingLength N b k) × Unit,
      ((F.posteriorEmpiricalLearner N b k
        (empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N))))
        (fun lam => max (4/5) (min beta lam)) (measurable_const.max (measurable_const.min measurable_id))).frozenRandomizedPolicy p.1 p.2).scalarObjective P
        (F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))
        (1-F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))-
      optimalCompetitiveRatio*(F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1)*P.expectedMaximum+
        1-F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1))
      ∂(P.reservoirLaw (trainingLength N b k)).prod (Measure.dirac ()) := by
  let rho := fun lam : ℝ => max (4/5 : ℝ) (min beta lam)
  have hRho : Measurable rho := measurable_const.max (measurable_const.min measurable_id)
  let e := empiricalBlockColumn b m (N+1) (h.trans ((trainingLength_le N b k).trans (Nat.le_succ N)))
  let L := F.posteriorEmpiricalLearner N b k e rho hRho
  let D : Measure (Reservoir n (trainingLength N b k) × Unit) :=
    (P.reservoirLaw (trainingLength N b k)).prod (Measure.dirac ())
  have hD : IsProbabilityMeasure D := by dsimp only [D];infer_instance
  let W := fun p : Reservoir n (trainingLength N b k) × Unit =>
    F.boundedPosteriorFromObservation N b k (extendTrainingPrefix n N b k p.1)
  have hW : Measurable W := (F.measurable_boundedPosteriorFromObservation N b k).comp
    ((measurable_extendTrainingPrefix n N b k).comp measurable_fst)
  have hUnit (p) : W p∈Icc (0 : ℝ) 1 := F.boundedPosteriorFromObservation_mem_unit N b k _
  have hRhoRange (lam : ℝ) (_hlam : lam∈Icc (0 : ℝ) 1) : rho lam∈Icc (4/5 : ℝ) beta :=
    ⟨le_max_left _ _,max_le hBeta.1.le (min_le_left _ _)⟩
  have hRhoUnit (p) : rho (W p)∈Icc (0 : ℝ) 1 :=
    ⟨(by norm_num : (0 : ℝ)≤4/5).trans (hRhoRange _ (hUnit p)).1,
      (hRhoRange _ (hUnit p)).2.trans hBeta.2.le⟩
  have hP := P.integrable_maximum_of_bounded hcap
  have hGap := P.integrable_normalizedGap_of_weight hcap D hW hUnit
  have hReg := @Learner.integrable_frozenNormalizedRegret n (trainingLength N b k) L P hP D hD
    (fun p => rho (W p)) (hRho.comp hW) hRhoUnit
  have hScore := @Learner.integrable_frozenSelectedScore n (trainingLength N b k) L P hP D hD
    W hW hUnit optimalCompetitiveRatio
  have hPoint (p : Reservoir n (trainingLength N b k) × Unit) :=
    hClamp (L.frozenRandomizedPolicy p.1 p.2) (W p)
      ((L.frozenRandomizedPolicy p.1 p.2).normalizedRegret P (rho (W p))) (hUnit p) le_rfl
  have hMean := integral_mono ((hGap.div_const 40).sub (hReg.const_mul 5)) hScore hPoint
  change (∫ p : Reservoir n (trainingLength N b k) × Unit,
    normalizedScalarGap P (W p)/40-5*(L.frozenRandomizedPolicy p.1 p.2).normalizedRegret P (rho (W p)) ∂D) ≤
    ∫ p : Reservoir n (trainingLength N b k) × Unit,
      (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P (W p) (1-W p)-
        optimalCompetitiveRatio*(W p*P.expectedMaximum+1-W p) ∂D at hMean
  rw [integral_sub (hGap.div_const 40) (hReg.const_mul 5),integral_div,integral_const_mul] at hMean
  have hBound := F.posteriorEmpirical_expected_regret_le N b k h hRho hBeta.2 hRhoRange P hcap hSmall
  change (∫ p : Reservoir n (trainingLength N b k) × Unit,
    (L.frozenRandomizedPolicy p.1 p.2).normalizedRegret P (rho (W p)) ∂D)≤_ at hBound
  have hFive := mul_le_mul_of_nonneg_left hBound (by norm_num : (0 : ℝ)≤5)
  have hFinal : (∫ p, normalizedScalarGap P (W p) ∂D)/40-
      5*(empiricalCapRegretConstant (1-beta)*(1+P.totalFirstMoment*(1+P.totalFirstMoment))/(m : ℝ)) ≤
      ∫ p, (L.frozenRandomizedPolicy p.1 p.2).scalarObjective P (W p) (1-W p)-
        optimalCompetitiveRatio*(W p*P.expectedMaximum+1-W p) ∂D := by
    linarith only [hMean,hFive]
  exact hFinal

end ProphetSecretary.Statistics.FinitePrior
