import ProphetSecretary.Probability.NormalizedScoreResponse

/-!
# Fixed-policy target derivatives and comparison of the two response scores

The auxiliary law, callbacks and scalar weights are fixed through the curve.
Benchmark terms cancel when two policies are compared, so both the normalized
scalar response and the reward-minus-duration target response are controlled
by the actual reward and duration score differences.
-/
open MeasureTheory Set
open scoped Classical Topology
namespace ProphetSecretary.Model
open ProphetSecretary.Probability
variable {n : ℕ}

noncomputable def RandomizedPolicy.targetScoreResponse (π : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) : ℝ :=
  π.expectedRewardScore P h-π.expectedDurationScore P h-optimalCompetitiveRatio*P.expectedMaximumScore h

theorem RandomizedPolicy.hasDerivAt_targetScoreResponse (π : RandomizedPolicy n) (P : Instance n)
    {H : ℝ} (hH : 0≤H) (hCap : ∀ i, ∀ᵐ x ∂P.law i, x≤H)
    (h : Fin n → ℝ → ℝ) (hh : ∀ i, Measurable (h i))
    (hb : ∀ i, ∀ᵐ x ∂P.law i, |h i x|≤1) (hm : ∀ i, (∫ x, h i x ∂P.law i)=0) :
    HasDerivAt (fun θ => π.expectedReward (P.likelihoodWidePath h hh hb hm θ)-
      π.expectedDuration (P.likelihoodWidePath h hh hb hm θ)-
      optimalCompetitiveRatio*((P.likelihoodWidePath h hh hb hm θ).expectedMaximum-1))
      (π.targetScoreResponse P h) 0 := by
  let Q := fun θ => P.likelihoodWidePath h hh hb hm θ
  have hP (θ) : Integrable Instance.maximum (Q θ).valuesLaw :=
    (Q θ).integrable_maximum_of_bounded (P.likelihoodWidePath_bounded h hh hb hm θ hCap)
  have hRF : (fun θ => π.scalarObjective (Q θ) 1 0)=(fun θ => π.expectedReward (Q θ)) := by
    funext θ
    rw [π.scalarObjective_eq (Q θ) (hP θ)]
    ring
  have hTF : (fun θ => π.scalarObjective (Q θ) 0 1)=(fun θ => π.expectedDuration (Q θ)) := by
    funext θ
    rw [π.scalarObjective_eq (Q θ) (hP θ)]
    ring
  have hR := π.hasDerivAt_scalarObjective_likelihoodWidePath_zero (w := 1) (c := 0) P hH hCap zero_le_one (le_refl 0) h hh hb hm
  have hT := π.hasDerivAt_scalarObjective_likelihoodWidePath_zero (w := 0) (c := 1) P hH hCap (le_refl 0) zero_le_one h hh hb hm
  change HasDerivAt (fun θ => π.scalarObjective (Q θ) 1 0) _ 0 at hR
  change HasDerivAt (fun θ => π.scalarObjective (Q θ) 0 1) _ 0 at hT
  rw [hRF,π.scalarLikelihoodDerivative_eq_scores P hH hCap h hh hb] at hR
  rw [hTF,π.scalarLikelihoodDerivative_eq_scores P hH hCap h hh hb] at hT
  simp only [one_mul,zero_mul,add_zero,zero_add] at hR hT
  have hM := P.hasDerivAt_expectedMaximum_likelihoodWidePath_zero hH hCap h hh hb hm
  exact hR.sub hT |>.sub ((hM.sub_const 1).const_mul optimalCompetitiveRatio)

lemma RandomizedPolicy.score_response_differences_le (π ρ : RandomizedPolicy n) (P : Instance n)
    (h : Fin n → ℝ → ℝ) {lam : ℝ} (hlam : lam∈Icc (0:ℝ) 1) :
    |π.normalizedScoreResponse P h lam-ρ.normalizedScoreResponse P h lam|≤
      |π.expectedRewardScore P h-ρ.expectedRewardScore P h|+|π.expectedDurationScore P h-ρ.expectedDurationScore P h| ∧
    |π.targetScoreResponse P h-ρ.targetScoreResponse P h|≤
      |π.expectedRewardScore P h-ρ.expectedRewardScore P h|+|π.expectedDurationScore P h-ρ.expectedDurationScore P h| := by
  let R := π.expectedRewardScore P h-ρ.expectedRewardScore P h
  let T := π.expectedDurationScore P h-ρ.expectedDurationScore P h
  have hA : π.normalizedScoreResponse P h lam-ρ.normalizedScoreResponse P h lam=lam*R+(1-lam)*T := by
    unfold RandomizedPolicy.normalizedScoreResponse R T
    ring
  have hB : π.targetScoreResponse P h-ρ.targetScoreResponse P h=R-T := by
    unfold RandomizedPolicy.targetScoreResponse R T
    ring
  constructor
  · rw [hA]
    apply (abs_add_le _ _).trans
    rw [abs_mul,abs_mul,abs_of_nonneg hlam.1,abs_of_nonneg (sub_nonneg.mpr hlam.2)]
    exact add_le_add
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hlam.2 (abs_nonneg R))
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right (show 1-lam≤1 by linarith only [hlam.1]) (abs_nonneg T))
  · rw [hB]
    exact abs_sub R T
end ProphetSecretary.Model
