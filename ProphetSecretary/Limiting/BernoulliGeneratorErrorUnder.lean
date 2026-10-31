import ProphetSecretary.Limiting.BernoulliGeneratorError

/-!
# Bernoulli design error under an original observation law

The design's current-state Poisson rate and target marginals are independent
of the laws whose observations drive the policy. The actual clock compensator
and constructed clock marginal give the same uniform error under those original
observations. This separation is needed for noninjective reserve shifts.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem HybridRule.bernoulliGenerator_integral_error_under (π : HybridRule (n + k) Seed) (hπ : π.IsMeasurable)
    (T : Model.Instance n) (P : Model.Instance (n + k)) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval)
    (hT : Integrable Model.Instance.maximum T.valuesLaw) (hI : Integrable id κ)
    (μ : FiniteMeasure ℝ) (hμ : (μ : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    (η : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let Q := finitePoissonDesign T κ hκ p k
    let ρ := (hybridWorldLaw P η ν).prod Model.Instance.uniformClock
    let C := (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2)
    Integrable (π.potentialGeneratorDrift Q (T.appendZeros k) κ μ w c) ρ ∧
      -C ≤ (∫ q, π.potentialGeneratorDrift Q (T.appendZeros k) κ μ w c q ∂ρ) ∧
      (∫ q, π.potentialGeneratorDrift Q (T.appendZeros k) κ μ w c q ∂ρ) ≤
        (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) + C := by
  let Q := finitePoissonDesign T κ hκ p k
  let ρ := (hybridWorldLaw P η ν).prod Model.Instance.uniformClock
  have hQ := finitePoissonDesign_integrable_maximum T κ hκ p k hT hI
  have hg (j : Fin k) := π.bernoulliPremiumGap_integral_bound hπ T P κ hκ p hT hI η ν hw hc j
  have hi (j : Fin k) : Integrable (fun q => π.bernoulliPremiumGap Q κ p w c j q) ρ := (hg j).1
  have hSI : Integrable (fun q => ∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ρ :=
    integrable_finsetSum _ (fun j _ => hi j)
  have hSN : 0 ≤ ∫ q, (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ∂ρ := by
    rw [integral_finsetSum _ (fun j _ => hi j)]
    exact Finset.sum_nonneg (fun j _ => (hg j).2.1)
  have hSU := π.sum_bernoulliPremiumGap_integral_bound hπ T P κ hκ p hT hI η ν hw hc
  have hcur := π.bernoulliCurrentError_integral_bound hπ Q P hQ κ hκ hI p η ν hw hc
  have hp (q : HybridWorld (n + k) Seed × ℝ) :
      π.potentialGeneratorDrift Q (T.appendZeros k) κ μ w c q =
        (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) + π.bernoulliCurrentError Q κ p w c q :=
    π.bernoulliGenerator_split T κ hκ p hT hI μ hμ hw.le hc q
  have hGI : Integrable (π.potentialGeneratorDrift Q (T.appendZeros k) κ μ w c) ρ :=
    (hSI.add hcur.1).congr (Filter.Eventually.of_forall fun q => (hp q).symm)
  have he : (∫ q, π.potentialGeneratorDrift Q (T.appendZeros k) κ μ w c q ∂ρ) =
      (∫ q, (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ∂ρ) +
        (∫ q, π.bernoulliCurrentError Q κ p w c q ∂ρ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hp),integral_add hSI hcur.1]
  refine ⟨hGI,?_,?_⟩
  · rw [he]
    have hl := (abs_le.mp hcur.2).1
    linarith only [hSN,hl]
  · rw [he]
    exact add_le_add hSU (abs_le.mp hcur.2).2

end ProphetSecretary.Limiting
