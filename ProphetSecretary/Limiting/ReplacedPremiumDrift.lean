import ProphetSecretary.Limiting.RarePoissonDesign
import ProphetSecretary.Limiting.PremiumHazardBound

/-!
# Centering the original replaced-offer generator

The actual sum of positive marginal measures supplies the Poisson mark law.
Consequently its total current premium agrees with the sum of original
premia. Centering the original unseen-clock generator gives exactly the signed
premium hazard error, including offers that arrive after the policy stops.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n m k : ℕ} {Seed : Type*}

noncomputable def HybridRule.replacedPremiumRaw (π : HybridRule (n + m + k) Seed)
    (Q : Model.Instance (n + m + k)) (R : Model.Instance m) (w c : ℝ)
    (q : HybridWorld (n + m + k) Seed × ℝ) : ℝ :=
  ∑ j, if q.2 ≤ π.realizedDuration q.1 ∧ q.2 < q.1.2.2.1 ((j.natAdd n).castAdd k) then
    Model.positivePremium (R.law j) w (poissonContinuation Q w c q.1.2.2.1 q.2) / (1 - q.2) else 0

noncomputable def HybridRule.replacedPremiumCurrentError (π : HybridRule (n + m + k) Seed)
    (Q : Model.Instance (n + m + k)) (R : Model.Instance m) (w c : ℝ)
    (q : HybridWorld (n + m + k) Seed × ℝ) : ℝ :=
  if q.2 ≤ π.realizedDuration q.1 then
    premiumHazardError R w (poissonContinuation Q w c q.1.2.2.1 q.2) q.2
      (fun j => q.1.2.2.1 ((j.natAdd n).castAdd k)) else 0

lemma HybridRule.replacedPremiumRaw_center (π : HybridRule (n + m + k) Seed)
    (Q : Model.Instance (n + m + k)) (R : Model.Instance m)
    (hQ : Integrable Model.Instance.maximum Q.valuesLaw) (hR : Integrable Model.Instance.maximum R.valuesLaw)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (q : HybridWorld (n + m + k) Seed × ℝ) :
    π.replacedPremiumRaw Q R w c q -
      π.poissonPotentialDrift Q (positiveOfferIntensity R).normalize (positiveOfferIntensity R) w c q =
        π.replacedPremiumCurrentError Q R w c q := by
  have hv := poissonContinuation_nonnegative Q hQ hw hc q.1.2.2.1 q.2
  have hmark := positiveOfferIntensity_normalized_premium R hR hw hv
  by_cases hs : q.2 ≤ π.realizedDuration q.1
  · unfold HybridRule.replacedPremiumRaw HybridRule.poissonPotentialDrift HybridRule.replacedPremiumCurrentError
    simp only [hs, true_and, if_true]
    rw [hmark]
    unfold premiumHazardError tailHazardError
    rw [Finset.sum_div]
    congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp
  · unfold HybridRule.replacedPremiumRaw HybridRule.poissonPotentialDrift HybridRule.replacedPremiumCurrentError
    simp only [hs, false_and, if_false, Finset.sum_const_zero, sub_self]

end ProphetSecretary.Limiting
