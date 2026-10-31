import ProphetSecretary.LowerBound.LikelihoodExperimentData
import ProphetSecretary.Probability.FiniteExperimentTaylor
import ProphetSecretary.Model.CompetitiveBasic

/-!
# Actual A and B Taylor controls for a finite likelihood experiment

The common remainder constant is 4(H+1)I. It is uniform over every array index
and every randomized policy. Its proof combines the actual reward, duration
and benchmark remainders with fixed normalized coefficients; no optimized
value or reoptimized stopping duration is differentiated.
-/
open MeasureTheory Set
open scoped Classical Topology
namespace ProphetSecretary.LowerBound
open ProphetSecretary.Model ProphetSecretary.Probability

private lemma abs_three_unit_coeff_le (R T M a b c : ℝ)
    (ha : a∈Icc (0:ℝ) 1) (hb : b∈Icc (0:ℝ) 1) (hc : c∈Icc (0:ℝ) 1) :
    |a*R+b*T-c*M|≤|R|+|T|+|M| := by
  have hMul (x d : ℝ) (hd : d∈Icc (0:ℝ) 1) : |d*x|≤|x| := by
    rw [abs_mul,abs_of_nonneg hd.1]
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hd.2 (abs_nonneg x)
  calc
    _ ≤ |a*R+b*T|+|c*M| := abs_sub _ _
    _ ≤ (|a*R|+|b*T|)+|c*M| := add_le_add (abs_add_le (a*R) (b*T)) (le_refl (|c*M|))
    _ ≤ _ := add_le_add (add_le_add (hMul R a ha) (hMul T b hb)) (hMul M c hc)

theorem likelihoodExperiment_taylor (sizes : ℕ → ℕ) (P : ∀ m, Instance (sizes m)) {H I : ℝ}
    (hH : 0≤H) (hI : 0≤I) (hCap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤H)
    (score : ∀ m, Fin (sizes m) → ℝ → ℝ) (hh : ∀ m i, Measurable (score m i))
    (hb : ∀ m i, ∀ᵐ x ∂(P m).law i, |score m i x|≤1)
    (hm : ∀ m i, (∫ x, score m i x ∂(P m).law i)=0) (lams : ℕ → ℝ)
    (hRange : ∀ m, lams m∈Icc (0:ℝ) 1) (hInfo : ∀ m, information (P m).law (score m)≤I) :
    let E := likelihoodExperiment sizes P score hh hb hm lams
    ∀ m (π : RandomizedPolicy (sizes m)) θ, |θ|≤1/4 →
      (|E.baseWeightGap m π θ-E.baseWeightGap m π 0-θ*deriv (E.baseWeightGap m π) 0|≤(4*(H+1)*I)*θ^2) ∧
      (|E.balanceDifference m π θ-E.balanceDifference m π 0-θ*deriv (E.balanceDifference m π) 0|≤(4*(H+1)*I)*θ^2) := by
  let E := likelihoodExperiment sizes P score hh hb hm lams
  dsimp only
  intro m π θ hθ
  let Q := fun t => (P m).likelihoodWidePath (score m) (hh m) (hb m) (hm m) t
  let R := π.expectedReward (Q θ)-π.expectedReward (P m)-θ*π.expectedRewardScore (P m) (score m)
  let T := π.expectedDuration (Q θ)-π.expectedDuration (P m)-θ*π.expectedDurationScore (P m) (score m)
  let M := (Q θ).expectedMaximum-(P m).expectedMaximum-θ*(P m).expectedMaximumScore (score m)
  have hTerms := finite_likelihood_payoff_taylor sizes P hH hCap score hh hb hm hInfo m π θ hθ
  change |R|≤2*H*θ^2*I ∧ |T|≤2*θ^2*I ∧ |M|≤2*H*θ^2*I at hTerms
  have hSum : |R|+|T|+|M|≤(4*(H+1)*I)*θ^2 := by
    apply (add_le_add (add_le_add hTerms.1 hTerms.2.1) hTerms.2.2).trans
    have hPos : 0≤I*θ^2 := mul_nonneg hI (sq_nonneg θ)
    nlinarith only [hPos]
  have hQ0 : Q 0=P m := (P m).likelihoodWidePath_zero_eq (score m) (hh m) (hb m) (hm m)
  have hP (t) : Integrable Instance.maximum (Q t).valuesLaw :=
    (Q t).integrable_maximum_of_bounded ((P m).likelihoodWidePath_bounded (score m) (hh m) (hb m) (hm m) t (hCap m))
  have hGap (t) : E.baseWeightGap m π t=
      lams m*π.expectedReward (Q t)+(1-lams m)*π.expectedDuration (Q t)-
        optimalCompetitiveRatio*(lams m*(Q t).expectedMaximum+1-lams m) := by
    change π.scalarObjective (Q t) (lams m) (1-lams m)-_=_
    rw [π.scalarObjective_eq (Q t) (hP t)]
    rfl
  have hAD : deriv (E.baseWeightGap m π) 0=π.normalizedScoreResponse (P m) (score m) (lams m) :=
    likelihoodExperiment_gap_deriv sizes P hH hCap score hh hb hm lams hRange m π
  have hBD : deriv (E.balanceDifference m π) 0=π.targetScoreResponse (P m) (score m) :=
    likelihoodExperiment_balance_deriv sizes P hH hCap score hh hb hm lams m π
  have hA : E.baseWeightGap m π θ-E.baseWeightGap m π 0-θ*deriv (E.baseWeightGap m π) 0=
      lams m*R+(1-lams m)*T-(optimalCompetitiveRatio*lams m)*M := by
    rw [hGap θ,hGap 0,hQ0,hAD]
    unfold RandomizedPolicy.normalizedScoreResponse R T M
    ring
  have hB : E.balanceDifference m π θ-E.balanceDifference m π 0-θ*deriv (E.balanceDifference m π) 0=
      R-T-optimalCompetitiveRatio*M := by
    change (π.expectedReward (Q θ)-π.expectedDuration (Q θ)-optimalCompetitiveRatio*((Q θ).expectedMaximum-1))-
      (π.expectedReward (Q 0)-π.expectedDuration (Q 0)-optimalCompetitiveRatio*((Q 0).expectedMaximum-1))-
      θ*deriv (E.balanceDifference m π) 0=_
    rw [hQ0,hBD]
    unfold RandomizedPolicy.targetScoreResponse R T M
    ring
  have hC : optimalCompetitiveRatio∈Icc (0:ℝ) 1 := ⟨optimalCompetitiveRatio_nonnegative,optimalCompetitiveRatio_le_one⟩
  have hCost : 1-lams m∈Icc (0:ℝ) 1 := ⟨sub_nonneg.mpr (hRange m).2,by linarith only [(hRange m).1]⟩
  have hCL : optimalCompetitiveRatio*lams m∈Icc (0:ℝ) 1 := by
    refine ⟨mul_nonneg hC.1 (hRange m).1,?_⟩
    have hProduct : optimalCompetitiveRatio*lams m≤lams m := by
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hC.2 (hRange m).1
    exact hProduct.trans (hRange m).2
  constructor
  · rw [hA]
    exact (abs_three_unit_coeff_le R T M (lams m) (1-lams m) (optimalCompetitiveRatio*lams m) (hRange m) hCost hCL).trans hSum
  · rw [hB]
    have h := abs_three_unit_coeff_le R (-T) M 1 1 optimalCompetitiveRatio (by norm_num) (by norm_num) hC
    have hBound : |R-T-optimalCompetitiveRatio*M|≤|R|+|T|+|M| := by
      simpa only [one_mul,abs_neg,sub_eq_add_neg] using h
    exact hBound.trans hSum
end ProphetSecretary.LowerBound
