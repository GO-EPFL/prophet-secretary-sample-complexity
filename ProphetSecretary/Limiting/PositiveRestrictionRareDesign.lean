import ProphetSecretary.Limiting.WeakRareDesign

/-!
# Quantitative value comparison from a full nonnegative mark law

A full analytical mark law may carry mass at zero, whereas the actual Poisson
intensity is its positive restriction. Their finite rare-offer marginals are
exactly equal. The actual hybrid policy class and observations are unchanged.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

theorem FiniteIntensityHybridInstance.rareDesign_full_mark_error
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (μ : FiniteMeasure ℝ) (H W R : ℝ≥0) (hCap : B.cap ≤ H)
    (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (heq : B.intensity = μ.restrict (Ioi 0)) (hrate : μ.mass ≤ R)
    (k : ℕ) (hk : 0 < k) (hkR : R ≤ (k : ℝ≥0))
    {w c : ℝ} (hw : 0 ≤ w) (hwW : w ≤ (W : ℝ)) (hc : 0 ≤ c) :
    |Model.optimalScalarValue (rareDesign B.individuals μ H hμ k hk (hrate.trans hkR)) w c - B.optimalScalarValue w c| ≤
      rareDesignError H W R k := by
  have hB : B.intensity.mass ≤ R := by
    rw [heq]
    exact (positiveRestriction_mass_le μ).trans hrate
  have hp := rareProbabilityLaw_positiveRestriction μ (hμ.mono fun _ hx => hx.1) k
    (by exact_mod_cast hk) (hrate.trans hkR)
  have hraw : rareFiniteLaw μ (k : ℝ≥0) = rareFiniteLaw (μ.restrict (Ioi 0)) (k : ℝ≥0) := by
    simpa only [rareProbabilityLaw_toFiniteMeasure] using congrArg ProbabilityMeasure.toFiniteMeasure hp
  have hdesign : rareDesign B.individuals μ H hμ k hk (hrate.trans hkR) =
      rareDesign B.individuals B.intensity B.cap
        (B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩) k hk (hB.trans hkR) := by
    apply Model.Instance.eq_of_law_eq
    funext i
    induction i using Fin.addCases with
    | left i => simp only [rareDesign,appendIID,Fin.addCases_left]
    | right j =>
      simp only [rareDesign,appendIID,Fin.addCases_right]
      change (rareFiniteLaw μ (k : ℝ≥0) : Measure ℝ) = (rareFiniteLaw B.intensity (k : ℝ≥0) : Measure ℝ)
      rw [hraw,heq]
  rw [hdesign]
  exact (B.rareDesign_value_uniform_error ha W R hB k hk hkR hw hwW hc).trans
    (rareDesignError_mono_cap hCap W R k)

end ProphetSecretary.Limiting
