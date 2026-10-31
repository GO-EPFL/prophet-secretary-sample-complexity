import ProphetSecretary.Statistics.PosteriorPilotMovement
import ProphetSecretary.Analysis.PosteriorResponse

/-!
# The low-first-moment Bayes response given the quadratic diameter bound

The clamp and pilot use one fixed interval. The diameter bound remains an
explicit hypothesis. All constants precede the finite prior and sample
count. The selected deployment index is deterministic, and the actual
learner requests fewer than 3m samples per distribution.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model ProphetSecretary.Analysis

theorem exists_lowMoment_posterior_response_of_quadratic_diameter
    (mu S0 : ℝ) (hS0 : 0≤S0)
    {beta Kc Kp D : ℝ} (hBeta : beta∈Ioo (4/5 : ℝ) 1)
    (hKc : 0≤Kc) (hKp : 0≤Kp) (hD : 0≤D)
    (hClamp : ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) → mu≤P.expectedMaximum →
      P.expectedMaximum≤1/80 → ∀ (π : RandomizedPolicy n) (lam r : ℝ), lam∈Icc (0 : ℝ) 1 →
      π.normalizedRegret P (max (4/5) (min beta lam))≤r →
      normalizedScalarGap P lam/40-5*r≤π.scalarObjective P lam (1-lam)-
        optimalCompetitiveRatio*(lam*P.expectedMaximum+1-lam))
    (hPilot : ∀ (n m : ℕ) [NeZero m] (P : Instance n) (G : Finset ℝ),
      (∀ i, ∀ᵐ x ∂P.law i, x≤1) → (∀ i, ∀ᵐ x ∂P.law i, x∈G) →
      mu≤P.expectedMaximum → P.expectedMaximum≤1/80 →
      (∫ y, normalizedScalarGap P
        (finiteGridPilotWeight G (4/5) beta (by norm_num) hBeta.2.le hBeta.1.le y)
        ∂P.trainingCoordinateLaw m)≤
        Kc*minimumNormalizedScalarGap P+Kp*(1+P.totalFirstMoment)^2/(m : ℝ))
    (hDiameter : ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) →
      mu≤P.expectedMaximum → P.totalFirstMoment≤S0 → ∀ a b : ℝ,
        a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
        (a-b)^2≤D*(normalizedScalarGap P a+normalizedScalarGap P b)) :
    ∃ K : ℝ, 0<K ∧ ∀ (n m : ℕ) [NeZero m], 8≤m → ∀ (F : FinitePrior n) (G : Finset ℝ),
      (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) →
      (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x∈G) →
      (∀ θ, mu≤(F.offerInstance θ).expectedMaximum) →
      (∀ θ, (F.offerInstance θ).expectedMaximum≤1/80) →
      (∀ θ, (F.offerInstance θ).totalFirstMoment≤S0) →
      ∃ k, 2*m≤k ∧ k<3*m ∧ -K/(m : ℝ)≤
        ∑ θ : Fin F.size, (F.weight θ : ℝ)*
          (F.posteriorEmpiricalLearner (3*m) 0 k
            (empiricalBlockColumn 0 m (3*m+1) (by omega))
            (fun lam => max (4/5) (min beta lam)) (measurable_const.max (measurable_const.min measurable_id))).targetGamePayoff (F.offerInstance θ) (F.target θ) optimalCompetitiveRatio := by
  have hlo : 0<1-beta := sub_pos.mpr hBeta.2
  have hlohi : 1-beta≤(1/4 : ℝ) := by linarith only [hBeta.1]
  let D1 := D*(1+Kc)
  let B := D*Kp*(1+S0)^2
  let E := 5*empiricalCapRegretConstant (1-beta)*(1+S0*(1+S0))
  have hD1 : 0≤D1 := by dsimp only [D1];positivity
  have hB : 0≤B := by dsimp only [B];positivity
  have hE : 0≤E := by
    have hK := (empiricalCapRegretConstant_positive hlo hlohi).le
    dsimp only [E]
    positivity
  let alpha := posteriorResponseAlpha (1/40) D1
  have hAlpha : 0<alpha := posteriorResponseAlpha_positive (by norm_num) hD1
  have hAlpha1 : alpha≤1 := posteriorResponseAlpha_le_one _ _
  have hAlphaD : alpha*D1≤(1/40 : ℝ)/2 := posteriorResponseAlpha_mul (by norm_num) hD1
  let K := posteriorResponseConstant (1/40) D1 B E
  have hK : 0<K := posteriorResponseConstant_positive (by norm_num) hD1 hB hE
  refine ⟨K,hK,?_⟩
  intro n m hm hM F G hcap hG hMean hSmall hS
  have hmPos : (0 : ℝ)<m := by exact_mod_cast (NeZero.pos m)
  let p := finitePriorPilot (n:=n) (3*m) m (by omega) G (4/5) beta (by norm_num) hBeta.2.le hBeta.1.le
  have hp : Measurable p := measurable_finitePriorPilot (by omega) G (4/5) beta (by norm_num) hBeta.2.le hBeta.1.le
  have hpu (d) : p d∈Icc (0 : ℝ) 1 := finitePriorPilot_mem_unit (by omega) G (4/5) beta (by norm_num) hBeta.2.le hBeta.1.le d
  have hPilotPrior : (∫ ω, normalizedScalarGap (F.offerInstance ω.1) (p (F.observe (3*m) 0 m ω)) ∂F.law (3*m))≤
      Kc*(∑ θ : Fin F.size, (F.weight θ : ℝ)*minimumNormalizedScalarGap (F.offerInstance θ))+
        Kp*(1+S0)^2/(m : ℝ) := by
    exact integral_finitePriorPilot_gap_le F (by omega) G hBeta hKp hcap hS
      (fun θ => hPilot n m (F.offerInstance θ) G (hcap θ) (hG θ) (hMean θ) (hSmall θ))
  obtain ⟨k,hLower,hUpper,_hBudget,hIncrement⟩ := F.exists_small_training_movement (3*m) 0 m (by omega) hM hAlpha hAlpha1 hp hpu
  have hDistance := F.posteriorPilotDistance_le_of_quadratic_diameter (3*m) k m hcap hp hpu hD hKc
    (fun θ a b ha hb => hDiameter n (F.offerInstance θ) (hcap θ) (hMean θ) (hS θ) a b ha hb) hPilotPrior
  change (∫ ω, (F.posterior (3*m) 0 k ω-p (F.observe (3*m) 0 m ω))^2 ∂F.law (3*m))≤
    D1*F.expectedPosteriorGap (3*m) 0 k+D*(Kp*(1+S0)^2/(m : ℝ)) at hDistance
  have hNorm : D*(Kp*(1+S0)^2/(m : ℝ))=B/(m : ℝ) := by dsimp only [B];ring
  rw [hNorm] at hDistance
  have hX := (F.expectedPosteriorGap_mem_unit (3*m) 0 k hcap).1
  have hControl := mul_le_mul_of_nonneg_left hDistance hAlpha.le
  have hAlphaDX := mul_le_mul_of_nonneg_right hAlphaD hX
  have hAlphaB := mul_le_of_le_one_left (div_nonneg hB hmPos.le) hAlpha1
  have hGame := F.posteriorEmpirical_game_lower_bound (m:=m) (3*m) 0 k (by unfold trainingLength;omega) (by omega)
    hBeta hcap hSmall (fun θ => hClamp n (F.offerInstance θ) (hcap θ) (hMean θ) (hSmall θ))
  have hError := F.posteriorEmpiricalError_le_of_firstMoment_bound (m:=m) hlo hlohi hS
  have hFive := mul_le_mul_of_nonneg_left hError (by norm_num : (0 : ℝ)≤5)
  have hNormE : 5*(empiricalCapRegretConstant (1-beta)*(1+S0*(1+S0))/(m : ℝ))=E/(m : ℝ) := by dsimp only [E];ring
  rw [hNormE] at hFive
  refine ⟨k,hLower,hUpper,?_⟩
  change -(E+B+8/alpha)/(m : ℝ)≤_
  have hNormI : 8/(alpha*(m : ℝ))=(8/alpha)/(m : ℝ) := by ring
  rw [hNormI] at hIncrement
  rw [neg_div,add_div,add_div]
  nlinarith only [hGame,hIncrement,hControl,hAlphaDX,hAlphaB,hFive,hX]

end ProphetSecretary.Statistics.FinitePrior
