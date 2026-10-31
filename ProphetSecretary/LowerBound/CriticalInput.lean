import ProphetSecretary.Limiting.IndividualCriticalLikelihoodFamily
import ProphetSecretary.Limiting.CloudCriticalLikelihoodFamily
import ProphetSecretary.Limiting.CriticalNormalizedLimit
import ProphetSecretary.Limiting.CountableLiftableDurationScore
import ProphetSecretary.LowerBound.LikelihoodExperimentControls

/-!
# Existence of the finite critical likelihood family

These are the actual normalized finite laws and reversed scores used in
`prop:critical-input`. Their cap, positive-tail profile, interior weights,
critical gaps, information and negative target response are proved together.
`likelihoodExperiment_controls` supplies the uniform likelihood remainder,
adaptive information, Taylor and derivative-stability estimates for this same
family. No bound on the total first moments is required.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.LowerBound
open ProphetSecretary.Model ProphetSecretary.Probability ProphetSecretary.Limiting

theorem exists_critical_likelihood_family :
    ∃ (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) (H δ I b : ℝ)
      (L : ℝ → ℝ) (lams : ℕ → ℝ) (score : ∀ m, Fin (sizes m) → ℝ → ℝ)
      (πopt : ∀ m, RandomizedPolicy (sizes m)),
      0≤H ∧ 0<δ ∧ δ<1/2 ∧ 0≤I ∧ 0<b ∧
      (∀ m j, ∀ᵐ x ∂(P m).law j, x≤H) ∧
      (∀ d, 0<d → 0≤L d) ∧
      (∀ m d, 0<d → (P m).tailCount d≤L d) ∧
      (∀ m, lams m∈Icc δ (1-δ)) ∧
      (∀ m, (P m).expectedMaximum=1) ∧
      Tendsto (fun m => normalizedScalarGap (P m) (lams m)) atTop (𝓝 (0 : ℝ)) ∧
      (∀ m j, Measurable (score m j)) ∧
      (∀ m j, ∀ᵐ x ∂(P m).law j, |score m j x|≤1) ∧
      (∀ m j, (∫ x, score m j x ∂(P m).law j)=0) ∧
      (∀ m, information (P m).law (score m)≤I) ∧
      (∀ m, (πopt m).scalarObjective (P m) (lams m) (1-lams m)=
        optimalScalarValue (P m) (lams m) (1-lams m)) ∧
      (∀ m, (πopt m).targetScoreResponse (P m) (score m)≤-b) := by
  obtain ⟨B,w,_hCap,hZero,hMean,hQuarter,hCritical,_hSequence⟩ :=
    exists_normalized_critical_ordered_limit
  have hw : 0<w := lt_of_lt_of_le (by norm_num : (0:ℝ)<1/4) hQuarter.1
  have hc : 0<1-w := by linarith only [hQuarter.2]
  have hSum : w+(1-w)=1 := by ring
  have hQuarterC : 1/4≤1-w := by linarith only [hQuarter.2]
  rcases B.exists_liftable_negative_duration_score hw hc hCritical with hIndividual|hCloud
  · obtain ⟨i,f,hNegative⟩ := hIndividual
    exact B.exists_individual_critical_likelihood_family hZero hMean hw hc hSum hCritical
      hQuarter.1 hQuarterC i f hNegative
  · obtain ⟨d,hd,hAtom,hNegative⟩ := hCloud
    have hAbove : (B.terminal : ℝ)<d := by simpa only [hZero,NNReal.coe_zero] using hd
    exact B.exists_cloud_critical_likelihood_family hZero hMean hw hc hSum hCritical
      hQuarter.1 hQuarterC d hAbove hAtom hNegative

/-- `prop:critical-input`, including all uniform statistical conditions and
the actual complete-likelihood remainder of the constructed family. -/
theorem critical_input :
    ∃ (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) (H α I b C B K : ℝ)
      (lams : ℕ → ℝ) (score : ∀ m, Fin (sizes m) → ℝ → ℝ)
      (hh : ∀ m i, Measurable (score m i))
      (hBound : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
      (hMean : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
      (πopt : ∀ m, RandomizedPolicy (sizes m)) (ω : ℝ → ℝ),
      let E := likelihoodExperiment sizes P score hh hBound hMean lams
      0≤H ∧ 0<α ∧ α<1/2 ∧ 0<I ∧ 0<b ∧ 0≤C ∧ 0≤B ∧ 0≤K ∧
      (∀ m, E.weight m∈Icc α (1-α)) ∧
      (∀ m θ, |θ|≤1/4 → ∀ i, ∀ᵐ x ∂(E.law m θ).law i, x≤H) ∧
      (∀ m, (E.law m 0).expectedMaximum=1) ∧
      (∀ m, (πopt m).scalarObjective (E.law m 0) (E.weight m) (1-E.weight m)=
        optimalScalarValue (E.law m 0) (E.weight m) (1-E.weight m)) ∧
      Tendsto (fun m => E.baseWeightGap m (πopt m) 0) atTop (𝓝 (0 : ℝ)) ∧
      Monotone ω ∧ (∀ s, 0≤s → 0≤ω s ∧ ω s≤B) ∧ ω 0=0 ∧
      Tendsto ω (𝓝[>] (0 : ℝ)) (𝓝 (0 : ℝ)) ∧
      (∀ m k (A : Learner (sizes m) k) t, |t|≤1/4 →
        InformationTheory.klDiv (A.transcriptLaw (E.law m t)) (A.transcriptLaw (E.law m (-t)))+
          InformationTheory.klDiv (A.transcriptLaw (E.law m (-t))) (A.transcriptLaw (E.law m t))≤
            ENNReal.ofReal (I*(k : ℝ)*t^2)) ∧
      (∀ m (π : RandomizedPolicy (sizes m)) θ, |θ|≤1/4 →
        (|E.baseWeightGap m π θ-E.baseWeightGap m π 0-θ*deriv (E.baseWeightGap m π) 0|≤C*θ^2) ∧
        (|E.balanceDifference m π θ-E.balanceDifference m π 0-θ*deriv (E.balanceDifference m π) 0|≤C*θ^2)) ∧
      (∀ m (π : RandomizedPolicy (sizes m)),
        |deriv (E.baseWeightGap m π) 0-deriv (E.baseWeightGap m (πopt m)) 0|+
          |deriv (E.balanceDifference m π) 0-deriv (E.balanceDifference m (πopt m)) 0|≤ω (E.scalarRegret m π)) ∧
      (∀ m, deriv (E.balanceDifference m (πopt m)) 0≤-b) ∧
      (∀ m, (∫ x, (completeScore (score m) x)^2 ∂(P m).valuesLaw)≤I) ∧
      (∀ m θ, |θ|≤1/4 →
        (∫ x, |likelihood (score m) θ x-1-θ*completeScore (score m) x| ∂(P m).valuesLaw)≤K*θ^2) := by
  obtain ⟨sizes,P,H,α,I,b,L,lams,score,πbase,hH,hα,hαhalf,hI,hb,hCap,hL,hTail,
    hRange,hNormalized,hCritical,hh,hBound,hMean,hInfo,hOptimal,hNegative⟩ :=
    exists_critical_likelihood_family
  have hInfo' (m : ℕ) : information (P m).law (score m)≤I+1 :=
    (hInfo m).trans (by linarith)
  let E := likelihoodExperiment sizes P score hh hBound hMean lams
  let πopt := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
    (hα.le.trans (hRange m).1)
    (show 0≤1-lams m from by linarith only [(hRange m).2,hα.le])
  obtain ⟨hCapPath,hOpt,_hScoreMean,hScoreSecond,hLikelihood,hKL,hTaylor,
    ω,hMono,hω,hωzero,hωlim,hResponse⟩ :=
    likelihoodExperiment_controls sizes P hH hα (by linarith : 0≤I+1) hCap L hL hTail
      lams hRange score hh hBound hMean hInfo'
  have hZero (m : ℕ) : E.law m 0=P m :=
    likelihoodExperiment_law_zero sizes P score hh hBound hMean lams m
  have hGap (m : ℕ) : E.baseWeightGap m (πopt m) 0=normalizedScalarGap (P m) (lams m) := by
    dsimp only [E,likelihoodExperiment,Experiment.baseWeightGap,Experiment.targetGap]
    rw [(P m).likelihoodWidePath_zero_eq (score m) (hh m) (hBound m) (hMean m)]
    dsimp only [πopt]
    rw [(P m).valuePolicy_optimal ((P m).integrable_maximum_of_bounded (hCap m))
      (hα.trans_le (hRange m).1)
      (show 0≤1-lams m from by linarith only [(hRange m).2,hα.le])]
    unfold normalizedScalarGap scalarGap
    ring
  have hRegret (m : ℕ) : (likelihoodExperiment sizes P score hh hBound hMean lams).scalarRegret m (πbase m)=0 := by
    dsimp only [likelihoodExperiment,Experiment.scalarRegret]
    rw [(P m).likelihoodWidePath_zero_eq (score m) (hh m) (hBound m) (hMean m),hOptimal m,sub_self]
  have hNeg (m : ℕ) : deriv (E.balanceDifference m (πopt m)) 0≤-b := by
    have hDiff := hResponse m (πbase m)
    rw [hRegret m,hωzero] at hDiff
    have hB : |deriv (E.balanceDifference m (πbase m)) 0-
        deriv (E.balanceDifference m (πopt m)) 0|≤0 := by
      have hA : 0≤|deriv (E.baseWeightGap m (πbase m)) 0-
          deriv (E.baseWeightGap m (πopt m)) 0| := abs_nonneg _
      linarith only [hDiff,hA]
    have hEq := sub_eq_zero.mp (abs_nonpos_iff.mp hB)
    rw [←hEq,likelihoodExperiment_balance_deriv sizes P hH hCap score hh hBound hMean lams]
    exact hNegative m
  refine ⟨sizes,P,H,α,16*(I+1),b,4*(H+1)*(I+1),
    2*Real.sqrt (2*(I+1)*(H+1)*(H+1)),2*(I+1),lams,score,hh,hBound,hMean,πopt,ω,
    hH,hα,hαhalf,by positivity,hb,by positivity,by positivity,by positivity,
    hRange,hCapPath,(fun m => by rw [hZero m]; exact hNormalized m),hOpt,?_,
    hMono,hω,hωzero,hωlim,hKL,hTaylor,hResponse,hNeg,?_,?_⟩
  · change Tendsto (fun m => E.baseWeightGap m (πopt m) 0) atTop (𝓝 (0 : ℝ))
    simpa only [hGap] using hCritical
  · intro m
    exact (hScoreSecond m).trans (by linarith only [hI])
  · intro m θ hθ
    exact (hLikelihood m θ hθ).trans_eq (by ring)

end ProphetSecretary.LowerBound
