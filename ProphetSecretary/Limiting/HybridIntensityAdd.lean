import ProphetSecretary.Limiting.RareDesignIntensityComparison
import ProphetSecretary.Limiting.HybridScalarGap

/-!
# Actual hybrid value increments from added finite intensity

A common virtual multiplicity is chosen for the two finite intensities before
the approximation limit. Finite stop-loss stability gives a first-moment
budget with no retained-dimension or duration-weight factor. No policy-thinning
or optimizer-convergence interface is assumed.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
open ProphetSecretary.Model
variable {n : ℕ}

lemma FiniteIntensityHybridInstance.commonRareDesign_value_tendsto
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (R : ℝ≥0) (hR : B.intensity.mass ≤ R)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Tendsto (fun j => Model.optimalScalarValue
      (rareDesign B.individuals B.intensity B.cap
        (B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩)
        (bernoulliMultiplicity (R : ℝ) j) (bernoulliMultiplicity_positive _ _)
        (hR.trans (nnreal_le_bernoulliMultiplicity R j))) w c)
      atTop (𝓝 (B.optimalScalarValue w c)) := by
  let W : ℝ≥0 := ⟨w,hw⟩
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ (rareDesignError_tendsto_zero B.cap W R)
  intro j
  simpa only [Real.norm_eq_abs] using B.rareDesign_value_uniform_error ha W R hR
    (bernoulliMultiplicity (R : ℝ) j) (bernoulliMultiplicity_positive _ _)
    (nnreal_le_bernoulliMultiplicity R j) hw le_rfl hc

/-- The actual zero-terminal hybrid optimum is monotone in added intensity
and its increase is at most reward weight times the added first moment. -/
theorem FiniteIntensityHybridInstance.value_intensity_add_zero_terminal
    (B D : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) (hd : D.terminal = 0)
    (hP : D.individuals = B.individuals)
    (ρ : FiniteMeasure ℝ) (hρ : ∀ᵐ x ∂(ρ : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap)
    (hIntensity : D.intensity = B.intensity+ρ) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    0 ≤ D.optimalScalarValue w c-B.optimalScalarValue w c ∧
      D.optimalScalarValue w c-B.optimalScalarValue w c ≤ w*(∫ x, x ∂(ρ : Measure ℝ)) := by
  let R := (B.intensity+ρ).mass
  have hRateB : B.intensity.mass ≤ R := finiteMeasure_mass_le_add _ _
  have hRateD : D.intensity.mass ≤ R := by rw [hIntensity]
  let ks := fun j => bernoulliMultiplicity (R : ℝ) j
  let hμ : ∀ᵐ x ∂(B.intensity : Measure ℝ), x ∈ Icc (0 : ℝ) B.cap :=
    B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩
  let hδ : ∀ᵐ x ∂(ρ : Measure ℝ), x ∈ Icc (0 : ℝ) B.cap := hρ.mono fun _ hx => ⟨hx.1.le,hx.2⟩
  let hs : ∀ᵐ x ∂((B.intensity+ρ : FiniteMeasure ℝ) : Measure ℝ), x ∈ Icc (0 : ℝ) B.cap :=
    ae_add_measure_iff.mpr ⟨hμ,hδ⟩
  let Qs := fun j => rareDesign B.individuals B.intensity B.cap hμ (ks j)
    (bernoulliMultiplicity_positive _ _) (hRateB.trans (nnreal_le_bernoulliMultiplicity R j))
  let Ts := fun j => rareDesign B.individuals (B.intensity+ρ) B.cap hs (ks j)
    (bernoulliMultiplicity_positive _ _) (nnreal_le_bernoulliMultiplicity R j)
  have hB : Tendsto (fun j => Model.optimalScalarValue (Qs j) w c) atTop (𝓝 (B.optimalScalarValue w c)) :=
    B.commonRareDesign_value_tendsto ha R hRateB hw hc
  have hEqD (j : ℕ) : Ts j = rareDesign D.individuals D.intensity D.cap
      (D.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩) (ks j)
      (bernoulliMultiplicity_positive _ _) (hRateD.trans (nnreal_le_bernoulliMultiplicity R j)) := by
    apply Model.Instance.eq_of_law_eq
    funext i
    induction i using Fin.addCases with
    | left i => simp only [Ts,rareDesign,appendIID,Fin.addCases_left,hP]
    | right j =>
      simp only [Ts,rareDesign,appendIID,Fin.addCases_right]
      change (rareFiniteLaw (B.intensity+ρ) (ks _ : ℝ≥0) : Measure ℝ) = (rareFiniteLaw D.intensity (ks _ : ℝ≥0) : Measure ℝ)
      rw [hIntensity]
  have hD : Tendsto (fun j => Model.optimalScalarValue (Ts j) w c) atTop (𝓝 (D.optimalScalarValue w c)) := by
    have h := D.commonRareDesign_value_tendsto hd R hRateD hw hc
    convert h using 1
    funext j
    rw [hEqD j]
  have hFinite (j : ℕ) : 0 ≤ Model.optimalScalarValue (Ts j) w c-Model.optimalScalarValue (Qs j) w c ∧
      Model.optimalScalarValue (Ts j) w c-Model.optimalScalarValue (Qs j) w c ≤ w*(∫ x, x ∂(ρ : Measure ℝ)) :=
    rareDesign_value_add_bounds B.individuals B.intensity ρ B.cap B.individual_bounded hμ hδ (ks j)
      (bernoulliMultiplicity_positive _ _) (nnreal_le_bernoulliMultiplicity R j) hw hc
  have hlim := hD.sub hB
  exact ⟨le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Eventually.of_forall fun j => (hFinite j).1),
    le_of_tendsto_of_tendsto hlim tendsto_const_nhds (Eventually.of_forall fun j => (hFinite j).2)⟩

end ProphetSecretary.Limiting
