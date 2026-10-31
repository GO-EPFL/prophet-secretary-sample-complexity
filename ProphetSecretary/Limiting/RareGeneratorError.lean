import ProphetSecretary.Limiting.RareGeneratorSplit
import ProphetSecretary.Limiting.ReplacedPremiumErrorBound
import ProphetSecretary.Limiting.BernoulliCurrentErrorBound

/-!
# Sharp original-law error plus vanishing virtual errors

The actual finite-law retained generator splits into the original sharp tail
error and two Bernoulli approximation errors. The bounds are uniform over all
measurable competing rules, including rules using every observed zero identity.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n m k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

theorem HybridRule.rare_retainedGenerator_integral_error (π : HybridRule (n + m + k) Seed) (hπ : π.IsMeasurable)
    (P : Model.Instance n) (R : Model.Instance m)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hR : Integrable Model.Instance.maximum R.valuesLaw)
    {H w c : ℝ} (hH : 0 ≤ H) (hcap : ∀ i, ∀ᵐ x ∂R.law i, x ≤ H) (hw : 0 < w) (hc : 0 ≤ c)
    (p : unitInterval) (hrate : (positiveOfferIntensity R : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    (hκ : ∀ᵐ x ∂((positiveOfferIntensity R).normalize : Measure ℝ), 0 ≤ x)
    (hI : Integrable id ((positiveOfferIntensity R).normalize : Measure ℝ))
    (η : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    let κ : Measure ℝ := (positiveOfferIntensity R).normalize
    let Q := rarePoissonDesign P κ hκ p m k
    let A := (P.appendIndependent R).appendZeros k
    let ρ := (hybridWorldLaw A η ν).prod Model.Instance.uniformClock
    let C := (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2)
    let D := (Real.pi / 2) * w * H * Real.sqrt (∑ i, distributionTail R 0 i ^ 2)
    Integrable (π.retainedPotentialDrift Q A w c) ρ ∧
      -(C + D) ≤ (∫ q, π.retainedPotentialDrift Q A w c q ∂ρ) ∧
      (∫ q, π.retainedPotentialDrift Q A w c q ∂ρ) ≤
        (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) + C + D := by
  let κ : Measure ℝ := (positiveOfferIntensity R).normalize
  let Q := rarePoissonDesign P κ hκ p m k
  let A := (P.appendIndependent R).appendZeros k
  let ρ := (hybridWorldLaw A η ν).prod Model.Instance.uniformClock
  have hQ := rarePoissonDesign_integrable_maximum P κ hκ p m k hP hI
  have hbase := P.appendZeros_integrable_maximum m hP
  have hg (j : Fin k) := π.bernoulliPremiumGap_integral_bound hπ (P.appendZeros m) A κ hκ p hbase hI η ν hw hc j
  have hgi (j : Fin k) : Integrable (fun q => π.bernoulliPremiumGap Q κ p w c j q) ρ := (hg j).1
  have hsumI : Integrable (fun q => ∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ρ :=
    integrable_finsetSum _ (fun j _ => hgi j)
  have hsumN : 0 ≤ ∫ q, (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ∂ρ := by
    rw [integral_finsetSum _ (fun j _ => hgi j)]
    exact Finset.sum_nonneg (fun j _ => (hg j).2.1)
  have hsumU := π.sum_bernoulliPremiumGap_integral_bound hπ (P.appendZeros m) A κ hκ p hbase hI η ν hw hc
  have hcur := π.bernoulliCurrentError_integral_bound hπ Q A hQ κ hκ hI p η ν hw hc
  have horig := π.replacedPremiumCurrentError_bound hπ Q A R hQ hH hcap hw hc η ν
  have hp (q : HybridWorld (n + m + k) Seed × ℝ) :
      π.retainedPotentialDrift Q A w c q =
        (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) + π.bernoulliCurrentError Q κ p w c q -
          π.replacedPremiumCurrentError Q R w c q :=
    π.rareGenerator_centered_split P R hP hR p hrate hw.le hc q hκ hI
  have hi : Integrable (π.retainedPotentialDrift Q A w c) ρ :=
    ((hsumI.add hcur.1).sub horig.1).congr (Filter.Eventually.of_forall fun q => (hp q).symm)
  have hplus : Integrable (fun q => (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) +
      π.bernoulliCurrentError Q κ p w c q) ρ := hsumI.add hcur.1
  have he : (∫ q, π.retainedPotentialDrift Q A w c q ∂ρ) =
      (∫ q, (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ∂ρ) +
        (∫ q, π.bernoulliCurrentError Q κ p w c q ∂ρ) -
          (∫ q, π.replacedPremiumCurrentError Q R w c q ∂ρ) := by
    rw [integral_congr_ae (Filter.Eventually.of_forall hp), integral_sub hplus horig.1,
      integral_add hsumI hcur.1]
  have hcl := (abs_le.mp hcur.2).1
  have hcu := (abs_le.mp hcur.2).2
  have hol := (abs_le.mp horig.2).1
  have hou := (abs_le.mp horig.2).2
  change Integrable (π.retainedPotentialDrift Q A w c) ρ ∧ _
  refine ⟨hi, ?_, ?_⟩
  · rw [he]
    linarith only [hsumN,hcl,hou]
  · rw [he]
    change (∫ q, (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) ∂ρ) ≤ _ at hsumU
    linarith only [hsumU,hcu,hol]

end ProphetSecretary.Limiting
