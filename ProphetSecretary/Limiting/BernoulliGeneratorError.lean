import ProphetSecretary.Limiting.BernoulliCurrentErrorBound

/-!
# Quantitative finite-Bernoulli to Poisson generator error

The exact signed generator split, quadratic child-state bound, and sharp
current-state hazard estimate give explicit uniform errors before the limit.
The estimate applies to every measurable shared hybrid policy and is uniform
in the number of retained individual variables.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem HybridRule.bernoulliGenerator_integral_error (π : HybridRule (n + k) Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    (μ : FiniteMeasure ℝ) (hμ : (μ : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    (ν : Measure Seed) [IsProbabilityMeasure ν] {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let Q := finitePoissonDesign P κ hκ p k
    let ρ := (hybridWorldLaw (P.appendZeros k) μ ν).prod Model.Instance.uniformClock
    let C := (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2)
    Integrable (π.potentialGeneratorDrift Q (P.appendZeros k) κ μ w c) ρ ∧
      -C ≤ (∫ q, π.potentialGeneratorDrift Q (P.appendZeros k) κ μ w c q ∂ρ) ∧
      (∫ q, π.potentialGeneratorDrift Q (P.appendZeros k) κ μ w c q ∂ρ) ≤
        (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) + C := by
  let Q := finitePoissonDesign P κ hκ p k
  let ρ := (hybridWorldLaw (P.appendZeros k) μ ν).prod Model.Instance.uniformClock
  let C := (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2)
  have hQ := finitePoissonDesign_integrable_maximum P κ hκ p k hP hI
  have hgap (j : Fin k) := π.bernoulliPremiumGap_integral_bound hπ P (P.appendZeros k) κ hκ p hP hI μ ν hw hc j
  have hi (j : Fin k) : Integrable (fun q => π.bernoulliPremiumGap Q κ p w c j q) ρ := (hgap j).1
  have hSI : Integrable (fun q => ∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ρ :=
    integrable_finsetSum _ (fun j _ => hi j)
  have hSU := π.sum_bernoulliPremiumGap_integral_bound hπ P (P.appendZeros k) κ hκ p hP hI μ ν hw hc
  have hSN : 0 ≤ ∫ q, (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ∂ρ := by
    rw [integral_finsetSum _ (fun j _ => hi j)]
    exact Finset.sum_nonneg (fun j _ => (hgap j).2.1)
  have hcur := π.bernoulliCurrentError_integral_bound hπ Q (P.appendZeros k) hQ κ hκ hI p μ ν hw hc
  have hpoint (q : HybridWorld (n + k) Seed × ℝ) :
      π.potentialGeneratorDrift Q (P.appendZeros k) κ μ w c q =
        (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) + π.bernoulliCurrentError Q κ p w c q :=
    π.bernoulliGenerator_split P κ hκ p hP hI μ hμ hw.le hc q
  have hGI : Integrable (π.potentialGeneratorDrift Q (P.appendZeros k) κ μ w c) ρ :=
    (hSI.add hcur.1).congr (Filter.Eventually.of_forall fun q => (hpoint q).symm)
  have heq : (∫ q, π.potentialGeneratorDrift Q (P.appendZeros k) κ μ w c q ∂ρ) =
      (∫ q, (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ∂ρ) +
        (∫ q, π.bernoulliCurrentError Q κ p w c q ∂ρ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoint), integral_add hSI hcur.1]
  refine ⟨hGI, ?_, ?_⟩
  · rw [heq]
    have hl := (abs_le.mp hcur.2).1
    linarith only [hSN, hl]
  · rw [heq]
    exact add_le_add hSU (abs_le.mp hcur.2).2

end ProphetSecretary.Limiting
