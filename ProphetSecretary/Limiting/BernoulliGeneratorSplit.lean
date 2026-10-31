import ProphetSecretary.Limiting.IndividualDriftLaws
import ProphetSecretary.Limiting.HybridGeneratorVerification
import ProphetSecretary.Limiting.HazardFluctuation

/-!
# Finite Bernoulli potential against the Poisson process

For a finite design with virtual rare offers and an actual hybrid process with
virtual zero identities, the retained generator is the sum of virtual child
premia. Subtracting the Poisson current premium leaves the quadratic child
error and the centered uniform-clock hazard error. The equality is pathwise.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n k : ℕ} {Seed : Type*}

noncomputable def HybridRule.bernoulliCurrentError (π : HybridRule (n + k) Seed)
    (Q : Model.Instance (n + k)) (κ : Measure ℝ) (p : unitInterval) (w c : ℝ)
    (q : HybridWorld (n + k) Seed × ℝ) : ℝ :=
  if q.2 ≤ π.realizedDuration q.1 then
    tailHazardError (fun _ : Fin k => (p : ℝ)) q.2 (fun j => q.1.2.2.1 (j.natAdd n)) *
      Model.positivePremium κ w (poissonContinuation Q w c q.1.2.2.1 q.2) else 0

lemma HybridRule.bernoulliGenerator_split (π : HybridRule (n + k) Seed)
    (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    (μ : FiniteMeasure ℝ) (hμ : (μ : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (q : HybridWorld (n + k) Seed × ℝ) :
    let Q := finitePoissonDesign P κ hκ p k
    π.potentialGeneratorDrift Q (P.appendZeros k) κ μ w c q =
      (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) + π.bernoulliCurrentError Q κ p w c q := by
  let Q := finitePoissonDesign P κ hκ p k
  have hQ := finitePoissonDesign_integrable_maximum P κ hκ p k hP hI
  have hleft (i : Fin n) : π.individualPotentialDrift Q (Q.law (i.castAdd k)) w c (i.castAdd k) q -
      π.individualPotentialDrift Q ((P.appendZeros k).law (i.castAdd k)) w c (i.castAdd k) q = 0 := by
    have hQi : Q.law (i.castAdd k) = P.law i := by
      simp only [Q, finitePoissonDesign, appendIID, Fin.addCases_left]
    have hPi : (P.appendZeros k).law (i.castAdd k) = P.law i := by
      simp only [Model.Instance.appendZeros, Fin.addCases_left]
    rw [hQi,hPi,sub_self]
  have hright (j : Fin k) : π.individualPotentialDrift Q (Q.law (j.natAdd n)) w c (j.natAdd n) q -
      π.individualPotentialDrift Q ((P.appendZeros k).law (j.natAdd n)) w c (j.natAdd n) q =
        (p : ℝ) * π.individualPotentialDrift Q κ w c (j.natAdd n) q := by
    have hQj : Q.law (j.natAdd n) = zeroInflatedLaw κ p := by
      simp only [Q, finitePoissonDesign, appendIID, Fin.addCases_right]
    have hPj : (P.appendZeros k).law (j.natAdd n) = Measure.dirac 0 := by
      simp only [Model.Instance.appendZeros, Fin.addCases_right]
    rw [hQj,hPj,π.individualPotentialDrift_zeroLaw Q hQ hw hc,
      π.individualPotentialDrift_zeroInflatedLaw Q hQ κ hI p hw hc,sub_zero]
  change (∑ i : Fin (n + k), (π.individualPotentialDrift Q (Q.law i) w c i q -
    π.individualPotentialDrift Q ((P.appendZeros k).law i) w c i q)) - π.poissonPotentialDrift Q κ μ w c q = _
  rw [Fin.sum_univ_add]
  simp_rw [hleft,hright]
  rw [Finset.sum_const_zero, zero_add]
  by_cases hs : q.2 ≤ π.realizedDuration q.1
  · unfold HybridRule.individualPotentialDrift HybridRule.poissonPotentialDrift
      HybridRule.bernoulliPremiumGap HybridRule.bernoulliCurrentError
    simp only [hs, true_and, if_true]
    rw [hμ]
    have hterm (j : Fin k) :
        (p : ℝ) * (if q.2 < q.1.2.2.1 (j.natAdd n) then
          individualDesignPremium Q κ w c (j.natAdd n) (q.2,q.1) / (1 - q.2) else 0) =
        (if q.2 < q.1.2.2.1 (j.natAdd n) then (p : ℝ) *
          (individualDesignPremium Q κ w c (j.natAdd n) (q.2,q.1) -
            Model.positivePremium κ w (poissonContinuation Q w c q.1.2.2.1 q.2)) / (1 - q.2) else 0) +
        (if q.2 < q.1.2.2.1 (j.natAdd n) then (p : ℝ) else 0) / (1 - q.2) *
          Model.positivePremium κ w (poissonContinuation Q w c q.1.2.2.1 q.2) := by
      split_ifs <;> ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_div]
    unfold tailHazardError
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  · unfold HybridRule.individualPotentialDrift HybridRule.poissonPotentialDrift
      HybridRule.bernoulliPremiumGap HybridRule.bernoulliCurrentError
    simp only [hs, false_and, if_false, mul_zero, Finset.sum_const_zero, sub_self, add_zero]

end ProphetSecretary.Limiting
