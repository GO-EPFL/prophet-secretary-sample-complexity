import ProphetSecretary.Statistics.FinitePriorClassifierAssembly
import ProphetSecretary.Statistics.HomogeneousBayesResponses
import ProphetSecretary.Statistics.BudgetGamePerformance

/-!
# Finite-prior Bayes responses with the actual classifier

One sample threshold and one constant precede every dimension, alphabet and
prior. Finite observable-cell normalization and fresh-response sampling give
the classifier bound. Padding to four times m preserves every actual payoff.
The explicit quadratic scalar diameter bound is the only structural input.
-/

open MeasureTheory Set
open scoped Classical BigOperators NNReal
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model ProphetSecretary.Analysis

theorem exists_finitePrior_bayes_response_of_scalarDiameter (mu : ℝ) (hmu : 0<mu)
    (hDiameter : ∀ S0 : ℝ, 0<S0 → ∃ D : ℝ, 0≤D ∧
      ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) →
      mu≤P.expectedMaximum → P.totalFirstMoment≤S0 → ∀ a b : ℝ,
      a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
      (a-b)^2≤D*(normalizedScalarGap P a+normalizedScalarGap P b)) :
    ∃ K : ℝ, ∃ m0 : ℕ, 0<K ∧ 65536≤m0 ∧
      ∀ (n m : ℕ) [NeZero m], m0≤m → ∀ (F : FinitePrior n) (G : Finset ℝ),
      (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) →
      (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x∈G) →
      (∀ θ, mu≤(F.offerInstance θ).expectedMaximum) →
      (∀ θ, (F.offerInstance θ).expectedMaximum≤1/80) →
      (∀ θ, (F.offerInstance θ).positiveCount≤2*Real.log (m : ℝ)) →
      ∃ L : Learner n (4*m),
        (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
        (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
        -K/(m : ℝ)≤∑ θ : Fin F.size, (F.weight θ : ℝ)*
          L.targetGamePayoff (F.offerInstance θ) (F.target θ) optimalCompetitiveRatio := by
  obtain ⟨beta,Sstar,K,m0,_hBeta,hSstar,hK,hm0,hAll⟩ :=
    exists_homogeneous_bayes_responses_of_scalarDiameter mu hmu hDiameter
  refine ⟨K+1,m0,by linarith only [hK],hm0,?_⟩
  intro n m _ hLarge F G hcap hG hMean hSmall hCount
  have hm : 2≤m := by omega
  have hmPos : (0 : ℝ)<m := by exact_mod_cast (show 0<m by omega)
  have hC : optimalCompetitiveRatio∈Icc (0 : ℝ) 1 :=
    ⟨optimalCompetitiveRatio_nonnegative,optimalCompetitiveRatio_le_one⟩
  have hResponse : ∀ (q : Fin F.size → ℝ≥0) (hq : 0<∑ θ, q θ) (low : Bool),
      (∀ θ : Fin (F.reweightedPrior q hq).size, 0<(F.reweightedPrior q hq).weight θ →
        if low=true then (F.offerInstance θ).totalFirstMoment≤3*Sstar
        else Sstar≤(F.offerInstance θ).totalFirstMoment) →
      ∃ L : Learner n (3*m),
        (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
        (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
        -(K/(m : ℝ))≤∑ θ : Fin (F.reweightedPrior q hq).size,
          ((F.reweightedPrior q hq).weight θ : ℝ)*L.targetGamePayoff
            ((F.reweightedPrior q hq).offerInstance θ) ((F.reweightedPrior q hq).target θ) optimalCompetitiveRatio := by
    intro q hq low hClass
    have hA := hAll n m hLarge (F.reweightedPrior q hq) G hcap hG hMean hSmall hCount
    cases low with
    | false =>
      have hHigh : ∀ θ : Fin (F.reweightedPrior q hq).size,
          0<(F.reweightedPrior q hq).weight θ → Sstar≤((F.reweightedPrior q hq).offerInstance θ).totalFirstMoment := by
        intro θ hθ
        exact hClass θ hθ
      simpa only [neg_div] using hA.2 hHigh
    | true =>
      have hLow : ∀ θ : Fin (F.reweightedPrior q hq).size,
          0<(F.reweightedPrior q hq).weight θ → ((F.reweightedPrior q hq).offerInstance θ).totalFirstMoment≤3*Sstar := by
        intro θ hθ
        exact hClass θ hθ
      simpa only [neg_div] using hA.1 hLow
  obtain ⟨L,hCap,hZero,hGame⟩ := F.exists_classifier_response_of_reweighted_responses G hm hcap hG
    hSstar hC (div_nonneg hK.le hmPos.le) hResponse
  have hBudget : classifierRounds m+3*m≤4*m := classifier_hard_budget_le_four_rounds (hm0.trans hLarge)
  refine ⟨L.padBudget hBudget,?_,?_,?_⟩
  · intro y r t i H
    rw [L.padBudget_decide]
    exact hCap _ _ _ _ _
  · intro y r t i H
    rw [L.padBudget_decide]
    exact hZero _ _ _ _ _
  · simp_rw [L.padBudget_targetGamePayoff]
    have hmOne : (1 : ℝ)≤m := by exact_mod_cast (show 1≤m by omega)
    have hPow : (m : ℝ)≤(m : ℝ)^4 := le_self_pow₀ hmOne (by norm_num)
    have hInv : 1/(m : ℝ)^4≤1/(m : ℝ) := one_div_le_one_div_of_le hmPos hPow
    calc
      -(K+1)/(m : ℝ)=-(K/(m : ℝ))-1/(m : ℝ) := by ring
      _≤-(K/(m : ℝ))-1/(m : ℝ)^4 := sub_le_sub_left hInv _
      _≤_ := hGame

end ProphetSecretary.Statistics.FinitePrior
