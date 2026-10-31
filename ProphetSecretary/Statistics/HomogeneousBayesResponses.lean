import ProphetSecretary.Statistics.LowMomentPosteriorResponse
import ProphetSecretary.Statistics.HighMomentPosteriorResponse
import ProphetSecretary.Statistics.PosteriorResponseBudget
import ProphetSecretary.Statistics.FinitePriorSupport

/-!
# Actual finite-prior responses in the two first-moment classes

One clamp interval and one sample threshold precede the instance size, alphabet,
prior, and sample count. Zero-weight atoms are removed before applying a class
response. The chosen learner has hard budget 3m and endpoint actions on every
raw input. The quadratic diameter theorem is the explicit remaining input to
this stage of `upbayes:theorem`.
-/

open MeasureTheory Set
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model

theorem exists_homogeneous_bayes_responses_of_scalarDiameter (mu : ℝ) (hmu : 0<mu)
    (hDiameter : ∀ S0 : ℝ, 0<S0 → ∃ D : ℝ, 0≤D ∧
      ∀ (n : ℕ) (P : Instance n), (∀ i, ∀ᵐ x ∂P.law i, x≤1) →
      mu≤P.expectedMaximum → P.totalFirstMoment≤S0 → ∀ a b : ℝ,
      a∈Icc (0 : ℝ) 1 → b∈Icc (0 : ℝ) 1 →
      (a-b)^2≤D*(normalizedScalarGap P a+normalizedScalarGap P b)) :
    ∃ beta Sstar K : ℝ, ∃ m0 : ℕ, beta∈Ioo (4/5 : ℝ) 1 ∧ 1≤Sstar ∧ 0<K ∧ 65536≤m0 ∧
      ∀ (n m : ℕ) [NeZero m], m0≤m → ∀ (F : FinitePrior n) (G : Finset ℝ),
      (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) →
      (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x∈G) →
      (∀ θ, mu≤(F.offerInstance θ).expectedMaximum) →
      (∀ θ, (F.offerInstance θ).expectedMaximum≤1/80) →
      (∀ θ, (F.offerInstance θ).positiveCount≤2*Real.log (m : ℝ)) →
      ((∀ θ, 0<F.weight θ → (F.offerInstance θ).totalFirstMoment≤3*Sstar) →
        ∃ L : Learner n (3*m),
          (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
          (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
          -K/(m : ℝ)≤∑ θ : Fin F.size, (F.weight θ : ℝ)*
            L.targetGamePayoff (F.offerInstance θ) (F.target θ) optimalCompetitiveRatio) ∧
      ((∀ θ, 0<F.weight θ → Sstar≤(F.offerInstance θ).totalFirstMoment) →
        ∃ L : Learner n (3*m),
          (∀ y r t i H, L.policy.decide (y,r) t i 1 H=true) ∧
          (∀ y r t i H, L.policy.decide (y,r) t i 0 H=false) ∧
          -K/(m : ℝ)≤∑ θ : Fin F.size, (F.weight θ : ℝ)*
            L.targetGamePayoff (F.offerInstance θ) (F.target θ) optimalCompetitiveRatio) := by
  obtain ⟨beta,hBeta,Kc,Kp,hKc,hKp,hAll⟩ := bounded_smallMean_clamp_and_pilot mu hmu
  have hClamp := fun n P hcap hMean hSmall => (hAll n P hcap hMean hSmall).1
  obtain ⟨Sstar,m0,hStar,hm0,hHigh⟩ := exists_highMoment_posterior_response_of_uniform_clamp mu hmu hBeta hClamp
  have hS0 : 0<3*Sstar := by linarith only [hStar]
  obtain ⟨D,hD,hDiam⟩ := hDiameter (3*Sstar) hS0
  obtain ⟨K,hK,hLow⟩ := exists_lowMoment_posterior_response_of_quadratic_diameter mu (3*Sstar) hS0.le
    hBeta hKc.le hKp.le hD hClamp
    (fun n m _ P G hcap hG hMean hSmall => (hAll n P hcap hMean hSmall).2 m G hG) hDiam
  refine ⟨beta,Sstar,K,m0,hBeta,hStar,hK,hm0,?_⟩
  intro n m hm hLarge F G hcap hG hMean hSmall hCount
  let A := F.positivePrior
  have hCapA (θ : Fin A.size) (i : Fin n) : ∀ᵐ x ∂(A.offerInstance θ).law i, x≤1 := hcap (F.positiveAtomEquiv θ) i
  have hGA (θ : Fin A.size) (i : Fin n) : ∀ᵐ x ∂(A.offerInstance θ).law i, x∈G := hG (F.positiveAtomEquiv θ) i
  have hMeanA (θ : Fin A.size) : mu≤(A.offerInstance θ).expectedMaximum := hMean (F.positiveAtomEquiv θ)
  have hSmallA (θ : Fin A.size) : (A.offerInstance θ).expectedMaximum≤1/80 := hSmall (F.positiveAtomEquiv θ)
  have hCountA (θ : Fin A.size) : (A.offerInstance θ).positiveCount≤2*Real.log (m : ℝ) := hCount (F.positiveAtomEquiv θ)
  constructor
  · intro hS
    have hSA (θ : Fin A.size) : (A.offerInstance θ).totalFirstMoment≤3*Sstar :=
      hS (F.positiveAtomEquiv θ) (F.positiveAtomEquiv θ).property
    obtain ⟨k,_hLower,_hUpper,hBound⟩ := hLow n m (by omega) A G hCapA hGA hMeanA hSmallA hSA
    let L := A.budgetedPosteriorResponse (m:=m) k beta
    refine ⟨L,(fun y r t i H => A.budgetedPosteriorResponse_accepts_cap k hBeta y r t i H),
      (fun y r t i H => A.budgetedPosteriorResponse_rejects_zero k beta y r t i H),?_⟩
    rw [←F.positivePrior_targetGamePayoff L optimalCompetitiveRatio]
    change -K/(m : ℝ)≤∑ θ : Fin A.size, (A.weight θ : ℝ)*L.targetGamePayoff
      (A.offerInstance θ) (A.target θ) optimalCompetitiveRatio
    simpa only [L,A.budgetedPosteriorResponse_targetGamePayoff] using hBound
  · intro hS
    have hSA (θ : Fin A.size) : Sstar≤(A.offerInstance θ).totalFirstMoment :=
      hS (F.positiveAtomEquiv θ) (F.positiveAtomEquiv θ).property
    obtain ⟨j,_hj,hBound⟩ := hHigh n m hLarge A hCapA hMeanA hSmallA hSA hCountA
    let L := A.budgetedPosteriorResponse (m:=m) (2*m+j) beta
    refine ⟨L,(fun y r t i H => A.budgetedPosteriorResponse_accepts_cap (2*m+j) hBeta y r t i H),
      (fun y r t i H => A.budgetedPosteriorResponse_rejects_zero (2*m+j) beta y r t i H),?_⟩
    rw [←F.positivePrior_targetGamePayoff L optimalCompetitiveRatio]
    change -K/(m : ℝ)≤∑ θ : Fin A.size, (A.weight θ : ℝ)*L.targetGamePayoff
      (A.offerInstance θ) (A.target θ) optimalCompetitiveRatio
    have hNonneg : 0≤∑ θ : Fin A.size, (A.weight θ : ℝ)*L.targetGamePayoff
        (A.offerInstance θ) (A.target θ) optimalCompetitiveRatio := by
      simpa only [L,A.budgetedPosteriorResponse_targetGamePayoff] using hBound
    exact (div_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hK.le) (Nat.cast_nonneg m)).trans hNonneg

end ProphetSecretary.Statistics.FinitePrior
