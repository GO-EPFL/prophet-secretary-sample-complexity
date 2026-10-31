import ProphetSecretary.Probability.FiniteNormalizationScorePayoffs
import ProphetSecretary.Probability.TargetScoreResponse

/-!
# A common normalized reversed target-score limit

All scales are the fixed unperturbed means. Actual product-law and fixed-policy
transport divide reward and prophet score means by those scales and preserve
duration score means. The same proof applies to individual and cloud scores.
No total-first-moment or instance-size bound is introduced.
-/

open MeasureTheory Set Filter
open scoped Classical Topology BigOperators
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

lemma RandomizedPolicy.targetScoreResponse_neg (π : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) : π.targetScoreResponse P (fun j x => -h j x)= -π.targetScoreResponse P h := by
  unfold RandomizedPolicy.targetScoreResponse RandomizedPolicy.expectedRewardScore
    RandomizedPolicy.expectedDurationScore Instance.expectedMaximumScore
  simp only [completeScore,Finset.sum_neg_distrib,neg_mul,integral_neg]
  ring

/-- A total analytical coefficient; only its positive-mean tail is retained
when constructing the normalized finite experiment. -/
noncomputable def RandomizedPolicy.fixedBaseNormalizedTargetScore (π : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) : ℝ :=
  let M := P.expectedMaximum
  (π.fixedBaseNormalizedPolicy M).targetScoreResponse
    (P.scale M⁻¹ (inv_nonneg.mpr P.expectedMaximum_nonnegative))
    (fun j y => -fixedBaseNormalizedScore M h j y)

lemma RandomizedPolicy.fixedBaseNormalizedTargetScore_eq (π : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) (hh : ∀ j, Measurable (h j)) (hM : 0<P.expectedMaximum) :
    π.fixedBaseNormalizedTargetScore P h=
      -(P.expectedMaximum⁻¹*(π.expectedRewardScore P h-optimalCompetitiveRatio*P.expectedMaximumScore h)-
        π.expectedDurationScore P h) := by
  unfold fixedBaseNormalizedTargetScore
  rw [π.fixedBaseNormalizedPolicy P.expectedMaximum |>.targetScoreResponse_neg]
  unfold RandomizedPolicy.targetScoreResponse
  rw [π.fixedBaseNormalization_rewardScore P hM h hh,π.fixedBaseNormalization_durationScore P hM h hh,
    P.fixedBaseNormalization_maximumScore hM h hh]
  ring

/-- Raw complete-score expectation limits imply the actual normalized,
parameter-reversed target coefficient limit. -/
theorem fixedBaseNormalizedTargetScore_tendsto (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m))
    (π : ∀ m, RandomizedPolicy (sizes m)) (h : ∀ m, Fin (sizes m) → ℝ → ℝ)
    (hh : ∀ m j, Measurable (h m j))
    (hMean : Tendsto (fun m => (P m).expectedMaximum) atTop (𝓝 (1 : ℝ)))
    {dR dT dM : ℝ}
    (hR : Tendsto (fun m => (π m).expectedRewardScore (P m) (h m)) atTop (𝓝 dR))
    (hT : Tendsto (fun m => (π m).expectedDurationScore (P m) (h m)) atTop (𝓝 dT))
    (hM : Tendsto (fun m => (P m).expectedMaximumScore (h m)) atTop (𝓝 dM)) :
    Tendsto (fun m => (π m).fixedBaseNormalizedTargetScore (P m) (h m)) atTop
      (𝓝 (-(dR-dT-optimalCompetitiveRatio*dM))) := by
  have hInv := hMean.inv₀ (by norm_num : (1 : ℝ)≠0)
  have hExpr := ((hInv.mul (hR.sub (hM.const_mul optimalCompetitiveRatio))).sub hT).neg
  change Tendsto (fun m => -((P m).expectedMaximum⁻¹*
    ((π m).expectedRewardScore (P m) (h m)-optimalCompetitiveRatio*(P m).expectedMaximumScore (h m))-
    (π m).expectedDurationScore (P m) (h m))) atTop
    (𝓝 (-((1 : ℝ)⁻¹*(dR-optimalCompetitiveRatio*dM)-dT))) at hExpr
  have hLimitEq : -((1 : ℝ)⁻¹*(dR-optimalCompetitiveRatio*dM)-dT)= -(dR-dT-optimalCompetitiveRatio*dM) := by
    rw [inv_one]
    ring
  rw [hLimitEq] at hExpr
  apply hExpr.congr'
  filter_upwards [hMean.eventually (lt_mem_nhds (by norm_num : (0 : ℝ)<1))] with m hm
  exact ((π m).fixedBaseNormalizedTargetScore_eq (P m) (h m) (hh m) hm).symm

end ProphetSecretary.Model
