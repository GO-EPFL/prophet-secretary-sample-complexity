import ProphetSecretary.Statistics.PosteriorLargeMomentGap
import ProphetSecretary.Statistics.PosteriorAverageRound
import ProphetSecretary.Analysis.LargeFirstMomentSurplus
import ProphetSecretary.Model.FirstMomentLayercake
import ProphetSecretary.Statistics.SmallMeanPilotBound

/-!
# An actual Bayes response in the high-first-moment class

The clamp interval is the one supplied by the proved uniform small-mean
package. Numerical thresholds are fixed before the finite prior and its
size. Posterior energy selects a deterministic deployment index; the
constructed learner queries fewer than 3m samples per distribution.
The low-first-moment response and its diameter dependency are separate.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model ProphetSecretary.Analysis

theorem exists_highMoment_posterior_response_of_uniform_clamp (mu : ℝ) (hmu : 0<mu)
    {beta : ℝ} (hBeta : beta∈Ioo (4/5 : ℝ) 1)
    (hClamp : ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum →
      P.expectedMaximum≤1/80 → ∀ (π : RandomizedPolicy n) (lam r : ℝ), lam∈Icc (0 : ℝ) 1 →
      π.normalizedRegret P (max (4/5) (min beta lam))≤r →
      normalizedScalarGap P lam/40-5*r≤π.scalarObjective P lam (1-lam)-
        optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam)) :
    ∃ Sstar : ℝ, ∃ m0 : ℕ, 1≤Sstar ∧ 65536≤m0 ∧
      ∀ (n m : ℕ) [NeZero m], m0≤m → ∀ F : FinitePrior n,
        (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) →
        (∀ θ, mu≤(F.offerInstance θ).expectedMaximum) →
        (∀ θ, (F.offerInstance θ).expectedMaximum≤1/80) →
        (∀ θ, Sstar≤(F.offerInstance θ).totalFirstMoment) →
        (∀ θ, (F.offerInstance θ).positiveCount≤2*Real.log (m : ℝ)) →
        ∃ j<m, 0≤∑ θ : Fin F.size, (F.weight θ : ℝ)*
          (F.posteriorEmpiricalLearner (3*m) 0 (2*m+j)
            (empiricalBlockColumn 0 m (3*m+1) (by omega))
            (fun lam => max (4/5) (min beta lam)) (measurable_const.max (measurable_const.min measurable_id))).targetGamePayoff (F.offerInstance θ) (F.target θ) optimalCompetitiveRatio := by
  obtain ⟨Sstar,κ,hStar,hκ,hFloor⟩ := exists_largeMoment_posterior_gap_floor mu hmu
  have hlo : 0<1-beta := sub_pos.mpr hBeta.2
  have hlohi : 1-beta≤(1/4 : ℝ) := by linarith only [hBeta.1]
  let K := empiricalCapRegretConstant (1-beta)
  have hK : 0<K := empiricalCapRegretConstant_positive hlo hlohi
  obtain ⟨m0,hm0,hSurplus⟩ := exists_largeFirstMomentSurplus_threshold
    (show 0<κ/40 by positivity) (show 0≤5*K by positivity)
  refine ⟨Sstar,m0,hStar,hm0,?_⟩
  intro n m hm hLargeM F hcap hMean hSmall hLarge hCount
  have hmPos : 0<m := NeZero.pos m
  have hmOne : (1 : ℝ)≤m := by exact_mod_cast hmPos
  have hLog : 0≤2*Real.log (m : ℝ) := mul_nonneg (by norm_num) (Real.log_nonneg hmOne)
  obtain ⟨j,hj,hIncrement⟩ := F.exists_inverse_round_posterior_increment (3*m) 0 m hmPos
  let k := 2*m+j
  have hk : 0+k<3*m := by dsimp only [k];omega
  have hEmp : 0+2*m≤trainingLength (3*m) 0 k := by unfold trainingLength;dsimp only [k];omega
  let rho := fun lam : ℝ => max (4/5 : ℝ) (min beta lam)
  have hRho : Measurable rho := measurable_const.max (measurable_const.min measurable_id)
  have hGame := F.posteriorEmpirical_game_lower_bound (3*m) 0 k hEmp hk hBeta hcap hSmall
    (fun θ => hClamp n (F.offerInstance θ) (hcap θ) (hMean θ) (hSmall θ))
  have hGap := hFloor n F (3*m) 0 k (2*Real.log (m : ℝ)) hLog hcap hMean hLarge hCount
  have hGap40 : (κ/40)/(1+2*Real.log (m : ℝ))^4≤F.expectedPosteriorGap (3*m) 0 k/40 := by
    calc
      _ = (κ/(1+2*Real.log (m : ℝ))^4)/40 := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hGap (by norm_num : (0 : ℝ)≤40)
  have hS (θ : Fin F.size) : (F.offerInstance θ).totalFirstMoment≤2*Real.log (m : ℝ) :=
    ((F.offerInstance θ).totalFirstMoment_le_positiveCount (hcap θ)).trans (hCount θ)
  have hError := F.posteriorEmpiricalError_le_of_firstMoment_bound (m:=m) hlo hlohi hS
  have hFive := mul_le_mul_of_nonneg_left hError (by norm_num : (0 : ℝ)≤5)
  have hNormalize : 5*(K*(1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)))/(m : ℝ))=
      (5*K)*(1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)))/(m : ℝ) := by ring
  change 5*F.posteriorEmpiricalError (1-beta) m≤
    5*(K*(1+(2*Real.log (m : ℝ))*(1+2*Real.log (m : ℝ)))/(m : ℝ)) at hFive
  rw [hNormalize] at hFive
  have hMargin := hSurplus m hLargeM
  let payoff := ∑ θ : Fin F.size, (F.weight θ : ℝ)*
    (F.posteriorEmpiricalLearner (3*m) 0 k (empiricalBlockColumn 0 m (3*m+1) (by omega)) rho hRho).targetGamePayoff (F.offerInstance θ) (F.target θ) optimalCompetitiveRatio
  change F.expectedPosteriorGap (3*m) 0 k/40-5*F.posteriorEmpiricalError (1-beta) m-
    Real.sqrt (∫ ω, (F.posterior (3*m) 0 (k+1) ω-F.posterior (3*m) 0 k ω)^2 ∂F.law (3*m))≤payoff at hGame
  refine ⟨j,hj,?_⟩
  change 0≤payoff
  change Real.sqrt (∫ ω, (F.posterior (3*m) 0 (k+1) ω-F.posterior (3*m) 0 k ω)^2 ∂F.law (3*m))≤
    1/Real.sqrt (m : ℝ) at hIncrement
  linarith only [hMargin,hGap40,hFive,hIncrement,hGame]

theorem exists_highMoment_posterior_response (mu : ℝ) (hmu : 0<mu) :
    ∃ beta : ℝ, beta∈Ioo (4/5 : ℝ) 1 ∧ ∃ Sstar : ℝ, ∃ m0 : ℕ,
      1≤Sstar ∧ 65536≤m0 ∧ ∀ (n m : ℕ) [NeZero m], m0≤m → ∀ F : FinitePrior n,
        (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) →
        (∀ θ, mu≤(F.offerInstance θ).expectedMaximum) →
        (∀ θ, (F.offerInstance θ).expectedMaximum≤1/80) →
        (∀ θ, Sstar≤(F.offerInstance θ).totalFirstMoment) →
        (∀ θ, (F.offerInstance θ).positiveCount≤2*Real.log (m : ℝ)) →
        ∃ j<m, 0≤∑ θ : Fin F.size, (F.weight θ : ℝ)*
          (F.posteriorEmpiricalLearner (3*m) 0 (2*m+j)
            (empiricalBlockColumn 0 m (3*m+1) (by omega))
            (fun lam => max (4/5) (min beta lam)) (measurable_const.max (measurable_const.min measurable_id))).targetGamePayoff (F.offerInstance θ) (F.target θ) optimalCompetitiveRatio := by
  obtain ⟨beta,hBeta,_Kc,_Kpilot,_hKc,_hKpilot,hAll⟩ := bounded_smallMean_clamp_and_pilot mu hmu
  obtain ⟨Sstar,m0,hStar,hm0,hResponse⟩ := exists_highMoment_posterior_response_of_uniform_clamp mu hmu hBeta
    (fun n P hcap hMean hSmall => (hAll n P hcap hMean hSmall).1)
  exact ⟨beta,hBeta,Sstar,m0,hStar,hm0,hResponse⟩

end ProphetSecretary.Statistics.FinitePrior
