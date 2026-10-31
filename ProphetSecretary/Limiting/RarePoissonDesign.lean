import ProphetSecretary.Limiting.IndependentAppend
import ProphetSecretary.Limiting.ZeroDesignContinuation
import ProphetSecretary.Limiting.BernoulliGeneratorSplit
import ProphetSecretary.Limiting.PositiveOfferIntensity

/-!
# A finite potential for retained and replaced original offers

The design keeps the retained laws, assigns zero laws to the original replaced
identities, and appends rare virtual Bernoulli marks. The competing execution
still sees every original identity and value; only the analytical design laws
are changed. Original replaced identities have exactly equal child/current
continuations, while virtual child errors are quadratic in their probability.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

variable {n m k : ℕ}

noncomputable def rarePoissonDesign (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (m k : ℕ) : Model.Instance (n + m + k) :=
  finitePoissonDesign (P.appendZeros m) κ hκ p k

lemma rarePoissonDesign_integrable_maximum (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (m k : ℕ)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ) :
    Integrable Model.Instance.maximum (rarePoissonDesign P κ hκ p m k).valuesLaw :=
  finitePoissonDesign_integrable_maximum (P.appendZeros m) κ hκ p k (P.appendZeros_integrable_maximum m hP) hI

lemma rarePoissonDesign_law_retained (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (m k : ℕ) (i : Fin n) :
    (rarePoissonDesign P κ hκ p m k).law ((i.castAdd m).castAdd k) = P.law i := by
  simp only [rarePoissonDesign, finitePoissonDesign, appendIID, Fin.addCases_left, Model.Instance.appendZeros]

lemma rarePoissonDesign_law_replaced (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (m k : ℕ) (j : Fin m) :
    (rarePoissonDesign P κ hκ p m k).law ((j.natAdd n).castAdd k) = Measure.dirac 0 := by
  simp only [rarePoissonDesign, finitePoissonDesign, appendIID, Fin.addCases_left,
    Model.Instance.appendZeros, Fin.addCases_right]

lemma rarePoissonDesign_law_virtual (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval) (m k : ℕ) (j : Fin k) :
    (rarePoissonDesign P κ hκ p m k).law (j.natAdd (n + m)) = zeroInflatedLaw κ p := by
  simp only [rarePoissonDesign, finitePoissonDesign, appendIID, Fin.addCases_right]

variable {Seed : Type*}

lemma HybridRule.replaced_individualDrift_eq_current (π : HybridRule (n + m + k) Seed)
    (P : Model.Instance n) (R : Model.Instance m) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (p : unitInterval)
    (hP : Integrable Model.Instance.maximum P.valuesLaw) (hI : Integrable id κ)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) (j : Fin m) (q : HybridWorld (n + m + k) Seed × ℝ) :
    let Q := rarePoissonDesign P κ hκ p m k
    π.individualPotentialDrift Q (R.law j) w c ((j.natAdd n).castAdd k) q =
      if q.2 ≤ π.realizedDuration q.1 ∧ q.2 < q.1.2.2.1 ((j.natAdd n).castAdd k) then
        Model.positivePremium (R.law j) w (poissonContinuation Q w c q.1.2.2.1 q.2) / (1 - q.2) else 0 := by
  have hQ := rarePoissonDesign_integrable_maximum P κ hκ p m k hP hI
  dsimp only
  unfold HybridRule.individualPotentialDrift individualDesignPremium
  rw [zero_design_childContinuation_eq_current _ hQ _ (rarePoissonDesign_law_replaced P κ hκ p m k j) hw hc]

end ProphetSecretary.Limiting
