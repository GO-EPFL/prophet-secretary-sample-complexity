import ProphetSecretary.Limiting.ReplacedPremiumDrift

/-!
# Original finite-law generator relative to a Bernoulli potential

All retained laws agree between design and execution. Original replaced laws
are zero only in the design, and virtual laws are zero only in the execution.
The actual finite generator is therefore the virtual-design generator minus
the original replaced-offer premia. No original observation is suppressed.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {n m k : ℕ} {Seed : Type*}

lemma HybridRule.rare_retainedGenerator_split (π : HybridRule (n + m + k) Seed)
    (P : Model.Instance n) (R : Model.Instance m) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (q : HybridWorld (n + m + k) Seed × ℝ) :
    let Q := rarePoissonDesign P κ hκ p m k
    π.retainedPotentialDrift Q ((P.appendIndependent R).appendZeros k) w c q =
      π.retainedPotentialDrift Q ((P.appendZeros m).appendZeros k) w c q - π.replacedPremiumRaw Q R w c q := by
  let Q := rarePoissonDesign P κ hκ p m k
  let S := (P.appendIndependent R).appendZeros k
  let Z := (P.appendZeros m).appendZeros k
  let D := fun (A : Model.Instance (n + m + k)) (i : Fin (n + m + k)) =>
    π.individualPotentialDrift Q (Q.law i) w c i q - π.individualPotentialDrift Q (A.law i) w c i q
  have hQ := rarePoissonDesign_integrable_maximum P κ hκ p m k hP hI
  have hSret (i : Fin n) : S.law ((i.castAdd m).castAdd k) = P.law i := by
    simp only [S, Model.Instance.appendZeros, Fin.addCases_left, Model.Instance.appendIndependent]
  have hZret (i : Fin n) : Z.law ((i.castAdd m).castAdd k) = P.law i := by
    simp only [Z, Model.Instance.appendZeros, Fin.addCases_left]
  have hretS (i : Fin n) : D S ((i.castAdd m).castAdd k) = 0 := by
    dsimp [D]
    rw [rarePoissonDesign_law_retained P κ hκ p m k i, hSret, sub_self]
  have hretZ (i : Fin n) : D Z ((i.castAdd m).castAdd k) = 0 := by
    dsimp [D]
    rw [rarePoissonDesign_law_retained P κ hκ p m k i, hZret, sub_self]
  have hSrare (j : Fin m) : S.law ((j.natAdd n).castAdd k) = R.law j := by
    simp only [S, Model.Instance.appendZeros, Fin.addCases_left, Model.Instance.appendIndependent, Fin.addCases_right]
  have hZrare (j : Fin m) : Z.law ((j.natAdd n).castAdd k) = Measure.dirac 0 := by
    simp only [Z, Model.Instance.appendZeros, Fin.addCases_left, Fin.addCases_right]
  have hrareS (j : Fin m) : D S ((j.natAdd n).castAdd k) =
      -(if q.2 ≤ π.realizedDuration q.1 ∧ q.2 < q.1.2.2.1 ((j.natAdd n).castAdd k) then
        Model.positivePremium (R.law j) w (poissonContinuation Q w c q.1.2.2.1 q.2) / (1 - q.2) else 0) := by
    dsimp [D]
    rw [rarePoissonDesign_law_replaced P κ hκ p m k j, hSrare,
      π.individualPotentialDrift_zeroLaw Q hQ hw hc,
      π.replaced_individualDrift_eq_current P R κ hκ p hP hI hw hc j q, zero_sub]
  have hrareZ (j : Fin m) : D Z ((j.natAdd n).castAdd k) = 0 := by
    dsimp [D]
    rw [rarePoissonDesign_law_replaced P κ hκ p m k j, hZrare, sub_self]
  have hvirtual (j : Fin k) : D S (j.natAdd (n + m)) = D Z (j.natAdd (n + m)) := by
    have hS : S.law (j.natAdd (n + m)) = Measure.dirac 0 := by
      simp only [S, Model.Instance.appendZeros, Fin.addCases_right]
    have hZ : Z.law (j.natAdd (n + m)) = Measure.dirac 0 := by
      simp only [Z, Model.Instance.appendZeros, Fin.addCases_right]
    dsimp [D]
    rw [hS,hZ]
  change (∑ i, D S i) = (∑ i, D Z i) - π.replacedPremiumRaw Q R w c q
  simp only [Fin.sum_univ_add]
  simp_rw [hretS,hretZ,hrareS,hrareZ,hvirtual]
  unfold HybridRule.replacedPremiumRaw
  simp only [Finset.sum_const_zero, zero_add, add_zero, Finset.sum_neg_distrib]
  ring

/-- Centering at the actual positive-offer intensity isolates the original
sharp tail error from the virtual Bernoulli approximation error. -/
lemma HybridRule.rareGenerator_centered_split (π : HybridRule (n + m + k) Seed)
    (P : Model.Instance n) (R : Model.Instance m)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hR : Integrable Model.Instance.maximum R.valuesLaw)
    (p : unitInterval)
    (hrate : (positiveOfferIntensity R : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (q : HybridWorld (n + m + k) Seed × ℝ)
    (hκ : ∀ᵐ x ∂((positiveOfferIntensity R).normalize : Measure ℝ), 0 ≤ x)
    (hI : Integrable id ((positiveOfferIntensity R).normalize : Measure ℝ)) :
    let κ : Measure ℝ := (positiveOfferIntensity R).normalize
    let Q := rarePoissonDesign P κ hκ p m k
    π.retainedPotentialDrift Q ((P.appendIndependent R).appendZeros k) w c q =
      (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) +
        π.bernoulliCurrentError Q κ p w c q - π.replacedPremiumCurrentError Q R w c q := by
  let κ : Measure ℝ := (positiveOfferIntensity R).normalize
  let Q := rarePoissonDesign P κ hκ p m k
  have hQ := rarePoissonDesign_integrable_maximum P κ hκ p m k hP hI
  have hs := π.rare_retainedGenerator_split P R κ hκ p hP hI hw hc q
  have hb := π.bernoulliGenerator_split (P.appendZeros m) κ hκ p
    (P.appendZeros_integrable_maximum m hP) hI (positiveOfferIntensity R) hrate hw hc q
  have hr := π.replacedPremiumRaw_center Q R hQ hR hw hc q
  dsimp only at hs hb ⊢
  change π.retainedPotentialDrift Q ((P.appendIndependent R).appendZeros k) w c q =
    π.retainedPotentialDrift Q ((P.appendZeros m).appendZeros k) w c q - π.replacedPremiumRaw Q R w c q at hs
  change π.replacedPremiumRaw Q R w c q - π.poissonPotentialDrift Q κ (positiveOfferIntensity R) w c q =
    π.replacedPremiumCurrentError Q R w c q at hr
  change π.retainedPotentialDrift Q ((P.appendZeros m).appendZeros k) w c q -
    π.poissonPotentialDrift Q κ (positiveOfferIntensity R) w c q =
      (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) + π.bernoulliCurrentError Q κ p w c q at hb
  change π.retainedPotentialDrift Q ((P.appendIndependent R).appendZeros k) w c q =
    (∑ j : Fin k, π.bernoulliPremiumGap Q κ p w c j q) + π.bernoulliCurrentError Q κ p w c q -
      π.replacedPremiumCurrentError Q R w c q
  linarith only [hs,hb,hr]

end ProphetSecretary.Limiting
