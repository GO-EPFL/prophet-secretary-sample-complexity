import ProphetSecretary.Statistics.PosteriorGapBounds
import ProphetSecretary.Model.LargeFirstMomentGapFloor

/-!
# A uniform posterior-gap floor for the high first-moment class

The constants precede the instance size, prior and sampling experiment.
Every posterior weight remains a unit-range observable; the lower bound
uses the actual minimum gap and the proved first-moment theorem, not an
assumed uniform first-moment bound near an arbitrary vanishing gap.
-/

open MeasureTheory Set
open scoped BigOperators
namespace ProphetSecretary.Statistics.FinitePrior
open ProphetSecretary.Model
variable {n : ℕ}

theorem exists_largeMoment_posterior_gap_floor (mu : ℝ) (hmu : 0<mu) :
    ∃ Sstar κ : ℝ, 1≤Sstar ∧ 0<κ ∧ ∀ (n : ℕ) (F : FinitePrior n) (N b k : ℕ) (L0 : ℝ),
      0≤L0 → (∀ θ i, ∀ᵐ x ∂(F.offerInstance θ).law i, x≤1) →
      (∀ θ, mu≤(F.offerInstance θ).expectedMaximum) →
      (∀ θ, Sstar≤(F.offerInstance θ).totalFirstMoment) →
      (∀ θ, (F.offerInstance θ).positiveCount≤L0) →
      κ/(1+L0)^4≤F.expectedPosteriorGap N b k := by
  obtain ⟨Sstar,κ,hStar,hκ,hFloor⟩ := bounded_largeFirstMoment_gap_floor mu hmu
  refine ⟨Sstar,κ,hStar,hκ,?_⟩
  intro n F N b k L0 hL0 hcap hMean hLarge hCount
  have hSum : (∑ θ : Fin F.size, (F.weight θ : ℝ))=1 := by exact_mod_cast F.weight_sum
  have hEach (θ : Fin F.size) : κ/(1+L0)^4≤minimumNormalizedScalarGap (F.offerInstance θ) := by
    have hL : 0≤(F.offerInstance θ).positiveCount := (F.offerInstance θ).tailCount_nonnegative 0
    have hDen : 0<(1+(F.offerInstance θ).positiveCount)^4 := by positivity
    have hPow : (1+(F.offerInstance θ).positiveCount)^4≤(1+L0)^4 :=
      pow_le_pow_left₀ (by positivity) (by linarith only [hCount θ]) _
    exact (div_le_div_of_nonneg_left hκ.le hDen hPow).trans
      (hFloor n (F.offerInstance θ) (hcap θ) (hMean θ) (hLarge θ))
  calc
    _ = ∑ θ : Fin F.size, (F.weight θ : ℝ)*(κ/(1+L0)^4) := by rw [←Finset.sum_mul,hSum,one_mul]
    _ ≤ ∑ θ : Fin F.size, (F.weight θ : ℝ)*minimumNormalizedScalarGap (F.offerInstance θ) :=
      Finset.sum_le_sum (fun θ _ => mul_le_mul_of_nonneg_left (hEach θ) (F.weight θ).coe_nonneg)
    _ ≤ _ := F.expectedPosteriorGap_ge_mean_minimum N b k hcap

end ProphetSecretary.Statistics.FinitePrior
