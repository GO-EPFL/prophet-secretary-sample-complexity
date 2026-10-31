import ProphetSecretary.LowerBound.LikelihoodExperimentControls
import ProphetSecretary.LowerBound.BayesLowerBound

/-!
# Applying the Bayesian bound to a centered finite likelihood family

The elementary properties of a finite family imply all uniform statistical
hypotheses of `thm:bayes`. The family, its criticality and its negative target
response are explicit inputs here; their existence is a separate result.
The likelihood parameter varies with each policy and its auxiliary law fixed.
-/

open MeasureTheory Set Filter
open scoped Classical Topology
namespace ProphetSecretary.LowerBound
open ProphetSecretary.Model ProphetSecretary.Probability

theorem likelihood_family_sample_lower_bound
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H δ I b : ℝ}
    (hH : 0≤H) (hδ : 0<δ) (hδhalf : δ<1/2) (hI : 0≤I) (hb : 0<b)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d)
    (hTail : ∀ m d, 0<d → (P m).tailCount d≤L d)
    (lams : ℕ → ℝ) (hRange : ∀ m, lams m∈Icc δ (1-δ))
    (hNormalized : ∀ m, (P m).expectedMaximum=1)
    (hCritical : Tendsto (fun m => normalizedScalarGap (P m) (lams m)) atTop (𝓝 (0 : ℝ)))
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hBound : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hMean : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I)
    (hNegative : ∀ m,
      ((P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
        (hδ.le.trans (hRange m).1)
        (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])).targetScoreResponse
          (P m) (score m)≤-b) :
    ∃ a eps0 : ℝ, 0<a ∧ 0<eps0 ∧ ∀ eps : ℝ, eps∈Ioo (0 : ℝ) eps0 →
      ∀ k : ℕ, FeasibleBudget eps k → a/eps≤(k : ℝ) := by
  let E := likelihoodExperiment sizes P score hh hBound hMean lams
  let πopt := fun m => (P m).valuePolicy ((P m).integrable_maximum_of_bounded (hCap m))
    (hδ.le.trans (hRange m).1)
    (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])
  have hInfo' (m : ℕ) : information (P m).law (score m)≤I+1 :=
    (hInfo m).trans (by linarith)
  obtain ⟨hCapPath,hOpt,_hScoreMean,_hScoreSecond,_hLikelihood,hKL,hTaylor,
    ω,hMono,hω,hωzero,hωlim,hResponse⟩ :=
    likelihoodExperiment_controls sizes P hH hδ (by linarith : 0≤I+1) hCap L hL hTail
      lams hRange score hh hBound hMean hInfo'
  have hZero (m : ℕ) : E.law m 0=P m :=
    likelihoodExperiment_law_zero sizes P score hh hBound hMean lams m
  have hGap (m : ℕ) : E.baseWeightGap m (πopt m) 0=normalizedScalarGap (P m) (lams m) := by
    dsimp only [E,likelihoodExperiment,Experiment.baseWeightGap,Experiment.targetGap]
    rw [(P m).likelihoodWidePath_zero_eq (score m) (hh m) (hBound m) (hMean m)]
    dsimp only [πopt]
    rw [(P m).valuePolicy_optimal ((P m).integrable_maximum_of_bounded (hCap m))
      (hδ.trans_le (hRange m).1)
      (show 0≤1-lams m from by linarith only [(hRange m).2,hδ.le])]
    unfold normalizedScalarGap scalarGap
    ring
  have hCritical' : Tendsto (fun m => E.baseWeightGap m (πopt m) 0) atTop (𝓝 (0 : ℝ)) := by
    simpa only [hGap] using hCritical
  apply E.bayes_sample_lower_bound πopt hδ hδhalf hH
    (show 0<16*(I+1) from by positivity) hb
    (show 0≤4*(H+1)*(I+1) from by positivity)
    (show 0<(1:ℝ)/4 from by norm_num)
    (show 0≤2*Real.sqrt (2*(I+1)*(H+1)*(H+1)) from by positivity)
    hRange hCapPath (fun m => by rw [hZero m]; exact hNormalized m) hOpt hCritical'
    ω hMono hω hωzero hωlim
  · intro m k A t ht hSmall
    exact hKL m k A t (by rwa [abs_of_pos ht])
  · exact hTaylor
  · exact hResponse
  · intro m
    rw [likelihoodExperiment_balance_deriv sizes P hH hCap score hh hBound hMean lams]
    exact hNegative m

/-- The same reduction permits any supplied actual base optimizer. At zero
regret, score stability makes its target response equal to the canonical one. -/
theorem likelihood_family_sample_lower_bound_of_optimal
    (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H δ I b : ℝ}
    (hH : 0≤H) (hδ : 0<δ) (hδhalf : δ<1/2) (hI : 0≤I) (hb : 0<b)
    (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (L : ℝ → ℝ) (hL : ∀ d, 0<d → 0≤L d)
    (hTail : ∀ m d, 0<d → (P m).tailCount d≤L d)
    (lams : ℕ → ℝ) (hRange : ∀ m, lams m∈Icc δ (1-δ))
    (hNormalized : ∀ m, (P m).expectedMaximum=1)
    (hCritical : Tendsto (fun m => normalizedScalarGap (P m) (lams m)) atTop (𝓝 (0 : ℝ)))
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hBound : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hMean : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0)
    (hInfo : ∀ m, information (P m).law (score m)≤I)
    (πopt : ∀ m, RandomizedPolicy (sizes m))
    (hOptimal : ∀ m, (πopt m).scalarObjective (P m) (lams m) (1-lams m)=
      optimalScalarValue (P m) (lams m) (1-lams m))
    (hNegative : ∀ m, (πopt m).targetScoreResponse (P m) (score m)≤-b) :
    ∃ a eps0 : ℝ, 0<a ∧ 0<eps0 ∧ ∀ eps : ℝ, eps∈Ioo (0 : ℝ) eps0 →
      ∀ k : ℕ, FeasibleBudget eps k → a/eps≤(k : ℝ) := by
  obtain ⟨Ω,_hΩ,_hMono,hZero,_hLimit,_hRoot,hResponse⟩ :=
    finite_uniform_response_stability sizes P hH hδ hI hCap L hL hTail lams hRange
      score hh hBound hMean hInfo
  apply likelihood_family_sample_lower_bound sizes P hH hδ hδhalf hI hb hCap L hL hTail
    lams hRange hNormalized hCritical score hh hBound hMean hInfo
  intro m
  have hRegret : optimalScalarValue (P m) (lams m) (1-lams m)-
      (πopt m).scalarObjective (P m) (lams m) (1-lams m)≤0 := by
    rw [hOptimal m,sub_self]
  have hDiff := (hResponse m (πopt m) 0 hRegret).2
  simp only [hZero,mul_zero,Real.sqrt_zero] at hDiff
  have hEq := sub_eq_zero.mp (abs_nonpos_iff.mp hDiff)
  rw [←hEq]
  exact hNegative m

end ProphetSecretary.LowerBound
