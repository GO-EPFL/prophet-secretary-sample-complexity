import ProphetSecretary.Limiting.FinitePoissonApproximation
import ProphetSecretary.Model.Truncation

/-!
# Capping finite Bernoulli designs and their aggregate excess

The zero atom is fixed by a nonnegative cap. Thus capping commutes with the
literal Bernoulli mixture, retaining every virtual zero identity. Summing
its actual marginal tail expectations gives k p times the mark excess.
-/

open MeasureTheory Set Filter
open scoped NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

lemma zeroInflatedLaw_map_cap (κ : Measure ℝ) (p : unitInterval) (K : ℝ≥0) :
    (zeroInflatedLaw κ p).map (Model.capValue K)=zeroInflatedLaw (κ.map (Model.capValue K)) p := by
  simp only [zeroInflatedLaw,Model.jackpotLaw]
  rw [Measure.map_add _ _ (Model.measurable_capValue K),Measure.map_smul,Measure.map_smul,
    Measure.map_dirac' (Model.measurable_capValue K)]
  have hz : Model.capValue K 0=0 := min_eq_left K.property
  rw [hz]

noncomputable def cappedMarkLaw (κ : ProbabilityMeasure ℝ) (K : ℝ≥0) : ProbabilityMeasure ℝ :=
  κ.map (Model.measurable_capValue K).aemeasurable

lemma cappedMarkLaw_nonnegative (κ : ProbabilityMeasure ℝ) (K : ℝ≥0)
    (hκ : ∀ᵐ x ∂(κ : Measure ℝ), 0≤x) :
    ∀ᵐ x ∂(cappedMarkLaw κ K : Measure ℝ), 0≤x := by
  change ∀ᵐ x ∂(κ : Measure ℝ).map (Model.capValue K), 0≤x
  apply (ae_map_iff (Model.measurable_capValue K).aemeasurable measurableSet_Ici).mpr
  exact hκ.mono fun _ hx => le_min hx K.property

lemma finitePoissonDesign_cap (P : Model.Instance n) (κ : ProbabilityMeasure ℝ)
    (hκ : ∀ᵐ x ∂(κ : Measure ℝ), 0≤x) (p : unitInterval) (k : ℕ) (K : ℝ≥0) :
    (finitePoissonDesign P (κ : Measure ℝ) hκ p k).cap K=
      finitePoissonDesign (P.cap K) (cappedMarkLaw κ K : Measure ℝ) (cappedMarkLaw_nonnegative κ K hκ) p k := by
  apply Model.Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases with
  | left i => simp only [Model.Instance.cap,finitePoissonDesign,appendIID,Fin.addCases_left]
  | right j =>
    simp only [Model.Instance.cap,finitePoissonDesign,appendIID,Fin.addCases_right]
    change (zeroInflatedLaw (κ : Measure ℝ) p).map (Model.capValue K)=
      zeroInflatedLaw ((κ : Measure ℝ).map (Model.capValue K)) p
    exact zeroInflatedLaw_map_cap _ p K

lemma finitePoissonDesign_tailSum (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0≤x) (p : unitInterval) (k : ℕ) (K : ℝ≥0) (hI : Integrable id κ) :
    (finitePoissonDesign P κ hκ p k).tailSum K=P.tailSum K+(k:ℝ)*(p:ℝ)*(∫ x, Model.tailValue K x ∂κ) := by
  have hTail := Model.integrable_tailValue κ hI K
  have hZero : Model.tailValue K 0=0 := by
    unfold Model.tailValue
    apply max_eq_right
    linarith only [K.property]
  have hVirtual : (∫ x, Model.tailValue K x ∂zeroInflatedLaw κ p)=(p:ℝ)*(∫ x, Model.tailValue K x ∂κ) := by
    rw [integral_zeroInflatedLaw κ p hTail,hZero,mul_zero,zero_add]
  change (∑ i : Fin (n+k), ∫ x, Model.tailValue K x ∂(finitePoissonDesign P κ hκ p k).law i)=_
  rw [Fin.sum_univ_add]
  simp only [finitePoissonDesign,appendIID,Fin.addCases_left,Fin.addCases_right,hVirtual,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Model.Instance.tailSum]
  ring

end ProphetSecretary.Limiting
