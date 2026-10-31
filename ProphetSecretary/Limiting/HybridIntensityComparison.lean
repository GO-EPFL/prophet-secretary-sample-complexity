import ProphetSecretary.Limiting.HybridIntensityAdd
import ProphetSecretary.Limiting.ExcessIntensityOrder

/-!
# Intensity monotonicity and a first-moment Lipschitz bound

The value is the actual supremum over all admissible randomized hybrid
policies. The proof passes common-size finite stop-loss comparisons to the
quantitative Poisson limit. Exact reserve removal and first-moment contraction
handle a common positive terminal reward. No thinning-policy interface or
canonical-optimizer assumption is used.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

/-- Adding positive finite mark intensity increases the actual value by at
most its first moment times reward weight. The constant is one, uniformly in
retained dimension and every nonnegative duration weight. -/
theorem FiniteIntensityHybridInstance.value_intensity_add
    (B D : FiniteIntensityHybridInstance n) (hTerm : D.terminal = B.terminal)
    (hP : D.individuals = B.individuals) (ρ : FiniteMeasure ℝ)
    (hρ : ∀ᵐ x ∂(ρ : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap)
    (hIntensity : D.intensity = B.intensity+ρ) {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    0 ≤ D.optimalScalarValue w c-B.optimalScalarValue w c ∧
      D.optimalScalarValue w c-B.optimalScalarValue w c ≤ w*(∫ x, x ∂(ρ : Measure ℝ)) := by
  by_cases hw0 : w = 0
  · subst w
    rw [D.value_zero_rewardWeight hc,B.value_zero_rewardWeight hc]
    simp
  have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
  have hPE : (D.excessState B.terminal).individuals = (B.excessState B.terminal).individuals :=
    congrArg (fun P => P.excessOffers (B.terminal : ℝ)) hP
  have hIE : (D.excessState B.terminal).intensity =
      (B.excessState B.terminal).intensity+excessIntensity ρ B.terminal := by
    change excessIntensity D.intensity B.terminal = excessIntensity B.intensity B.terminal+_
    rw [hIntensity,excessIntensity_add]
  have hδ := excessIntensity_supported ρ B.terminal.property hρ
  have hV := (B.excessState B.terminal).value_intensity_add_zero_terminal (D.excessState B.terminal)
    rfl rfl hPE (excessIntensity ρ B.terminal) hδ hIE hw hc
  have hMoment := excessIntensity_firstMoment_le ρ B.terminal B.cap
    (hρ.mono fun _ hx => ⟨hx.1.le,hx.2⟩)
  rw [D.value_reserveShift hwP hc,B.value_reserveShift hwP hc,hTerm]
  simp only [add_sub_add_left_eq_sub]
  exact ⟨hV.1,hV.2.trans (mul_le_mul_of_nonneg_left hMoment hw)⟩

/-- Ordered actual finite intensities. The added law is the genuine measure
ν−μ, constructed from measure subtraction rather than supplied as a policy
coupling. Zero intensity and zero expected maximum are included. -/
theorem FiniteIntensityHybridInstance.value_intensity_mono_lipschitz
    (B D : FiniteIntensityHybridInstance n) (hCap : D.cap ≤ B.cap)
    (hTerm : D.terminal = B.terminal) (hP : D.individuals = B.individuals)
    (hOrder : (B.intensity : Measure ℝ) ≤ (D.intensity : Measure ℝ))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    0 ≤ D.optimalScalarValue w c-B.optimalScalarValue w c ∧
      D.optimalScalarValue w c-B.optimalScalarValue w c ≤
        w*(∫ x, x ∂((D.intensity : Measure ℝ)-(B.intensity : Measure ℝ))) := by
  let ρ := finiteIntensityDifference D.intensity B.intensity
  have hρ : ∀ᵐ x ∂(ρ : Measure ℝ), x ∈ Ioc (0 : ℝ) B.cap :=
    (finiteIntensityDifference_supported D.intensity B.intensity D.intensity_supported).mono
      fun _ hx => ⟨hx.1,hx.2.trans (by exact_mod_cast hCap)⟩
  have hI : D.intensity = B.intensity+ρ := (add_finiteIntensityDifference _ _ hOrder).symm
  exact B.value_intensity_add D hTerm hP ρ hρ hI hw hc

lemma FiniteIntensityHybridInstance.optimalScalarValue_mono_intensity
    (B D : FiniteIntensityHybridInstance n) (hCap : D.cap ≤ B.cap)
    (hTerm : D.terminal = B.terminal) (hP : D.individuals = B.individuals)
    (hOrder : (B.intensity : Measure ℝ) ≤ (D.intensity : Measure ℝ))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : B.optimalScalarValue w c ≤ D.optimalScalarValue w c :=
  sub_nonneg.mp (B.value_intensity_mono_lipschitz D hCap hTerm hP hOrder hw hc).1

end ProphetSecretary.Limiting
