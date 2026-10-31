import ProphetSecretary.Limiting.FiniteBandArrayLikelihood
import ProphetSecretary.Limiting.ZeroIntensity

/-!
# Actual Poisson likelihood under finite-band intensity scaling

The Poisson mixing weights cancel the normalized-array mass factors.
The resulting likelihood uses the complete band count, including points after
stopping. Zero total intensity is handled by its actual empty configuration.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting

noncomputable def bandPoissonLikelihood (μ : FiniteMeasure ℝ) (S : Set ℝ) (r : ℝ≥0)
    (ω : Configuration) : ℝ :=
  Real.exp ((μ.mass : ℝ)-((bandScaledIntensity μ S r).mass : ℝ)) *
    (r : ℝ)^(pointCount (univ ×ˢ S) ω)

lemma measurable_bandPoissonLikelihood (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (r : ℝ≥0) : Measurable (bandPoissonLikelihood μ S r) :=
  ((measurable_of_countable (fun N : ℕ => (r : ℝ)^N)).comp
    (measurable_pointCount (MeasurableSet.univ.prod hS))).const_mul _

lemma bandPoissonLikelihood_eq (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) (r : ℝ≥0) (ω : Configuration) :
    bandPoissonLikelihood μ S r ω=
      Real.exp ((1-(r : ℝ))*(μ S : ℝ))*(r : ℝ)^(pointCount (univ ×ˢ S) ω) := by
  have hMass := bandScaledIntensity_mass_difference μ hS r
  have he : (μ.mass : ℝ)-((bandScaledIntensity μ S r).mass : ℝ)=(1-(r : ℝ))*(μ S : ℝ) := by
    linarith only [hMass]
  exact congrArg (fun t => Real.exp t*(r : ℝ)^(pointCount (univ ×ˢ S) ω)) he

lemma poissonWeight_normalization_cancel (μ ν : FiniteMeasure ℝ) (hν : ν ≠ 0) (N : ℕ) :
    poissonWeight ν.mass N*(((μ.mass/ν.mass : ℝ≥0) : ℝ)^N)=
      Real.exp ((μ.mass : ℝ)-(ν.mass : ℝ))*poissonWeight μ.mass N := by
  have hMassNN := ν.mass_nonzero_iff.mpr hν
  have hMassReal : (ν.mass : ℝ) ≠ 0 := by exact_mod_cast hMassNN
  have hCancel : (ν.mass : ℝ)*((μ.mass/ν.mass : ℝ≥0) : ℝ)=(μ.mass : ℝ) := by
    rw [NNReal.coe_div]
    exact mul_div_cancel₀ _ hMassReal
  have hPower : (ν.mass : ℝ)^N*(((μ.mass/ν.mass : ℝ≥0) : ℝ)^N)=(μ.mass : ℝ)^N := by
    rw [← mul_pow,hCancel]
  have hExp : Real.exp ((μ.mass : ℝ)-(ν.mass : ℝ))*Real.exp (-(μ.mass : ℝ))=
      Real.exp (-(ν.mass : ℝ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  unfold poissonWeight
  calc
    _ = Real.exp (-(ν.mass : ℝ))*(((ν.mass : ℝ)^N*(((μ.mass/ν.mass : ℝ≥0) : ℝ)^N))/(N.factorial : ℝ)) := by ring
    _ = Real.exp (-(ν.mass : ℝ))*((μ.mass : ℝ)^N/(N.factorial : ℝ)) := by rw [hPower]
    _ = (Real.exp ((μ.mass : ℝ)-(ν.mass : ℝ))*Real.exp (-(μ.mass : ℝ)))*
        ((μ.mass : ℝ)^N/(N.factorial : ℝ)) := by rw [hExp]
    _ = _ := by ring

lemma poissonFiber_bandScale_likelihood (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) {r : ℝ≥0} (hr : 0 < r) (hμ : μ ≠ 0) (N : ℕ) :
    ENNReal.ofReal (poissonWeight (bandScaledIntensity μ S r).mass N) •
        fiberLaw (bandScaledIntensity μ S r) N=
      (ENNReal.ofReal (poissonWeight μ.mass N) • fiberLaw μ N).withDensity
        (fun ω => ENNReal.ofReal (bandPoissonLikelihood μ S r ω)) := by
  let ν := bandScaledIntensity μ S r
  have hν : ν ≠ 0 := bandScaledIntensity_ne_zero μ hS hr hμ
  have hCount : ∀ᵐ ω ∂fiberLaw μ N, ω.1=N := by
    have hMP : MeasurePreserving (fun ω : Configuration => ω.1) (fiberLaw μ N) (Measure.dirac N) :=
      ⟨measurable_configuration_count,fiberLaw_count_map μ N⟩
    have hDirac : ∀ᵐ k : ℕ ∂Measure.dirac N, k=N := by simp
    exact hMP.quasiMeasurePreserving.ae hDirac
  have hCoefficient := poissonWeight_normalization_cancel μ ν hν N
  have hReal : ∀ᵐ ω ∂fiberLaw μ N,
      poissonWeight ν.mass N*bandNormalizedConfigurationDensity μ S r ω=
        poissonWeight μ.mass N*bandPoissonLikelihood μ S r ω := by
    filter_upwards [hCount] with ω hω
    change poissonWeight ν.mass N*
      ((((μ.mass/ν.mass : ℝ≥0) : ℝ)^ω.1)*(r : ℝ)^(pointCount (univ ×ˢ S) ω))=
        poissonWeight μ.mass N*(Real.exp ((μ.mass : ℝ)-(ν.mass : ℝ))*
          (r : ℝ)^(pointCount (univ ×ˢ S) ω))
    rw [hω]
    calc
      _ = (poissonWeight ν.mass N*(((μ.mass/ν.mass : ℝ≥0) : ℝ)^N))*
          (r : ℝ)^(pointCount (univ ×ˢ S) ω) := by ring
      _ = _ := by rw [hCoefficient]; ring
  have hOldNonnegative : 0 ≤ poissonWeight μ.mass N := by unfold poissonWeight; positivity
  have hNewNonnegative : 0 ≤ poissonWeight ν.mass N := by unfold poissonWeight; positivity
  have hENN :
      (ENNReal.ofReal (poissonWeight ν.mass N) •
        (fun ω => ENNReal.ofReal (bandNormalizedConfigurationDensity μ S r ω))) =ᵐ[ fiberLaw μ N]
      (ENNReal.ofReal (poissonWeight μ.mass N) •
        (fun ω => ENNReal.ofReal (bandPoissonLikelihood μ S r ω))) := by
    filter_upwards [hReal] with ω hω
    change ENNReal.ofReal (poissonWeight ν.mass N)*ENNReal.ofReal (bandNormalizedConfigurationDensity μ S r ω)=
      ENNReal.ofReal (poissonWeight μ.mass N)*ENNReal.ofReal (bandPoissonLikelihood μ S r ω)
    calc
      _ = ENNReal.ofReal (poissonWeight ν.mass N*bandNormalizedConfigurationDensity μ S r ω) :=
        (ENNReal.ofReal_mul hNewNonnegative).symm
      _ = ENNReal.ofReal (poissonWeight μ.mass N*bandPoissonLikelihood μ S r ω) := congrArg ENNReal.ofReal hω
      _ = _ := ENNReal.ofReal_mul hOldNonnegative
  calc
    _ = ENNReal.ofReal (poissonWeight ν.mass N) • (fiberLaw μ N).withDensity
        (fun ω => ENNReal.ofReal (bandNormalizedConfigurationDensity μ S r ω)) := by
      rw [fiberLaw_bandScale_configurationDensity μ hS hr hμ N]
    _ = (fiberLaw μ N).withDensity (ENNReal.ofReal (poissonWeight ν.mass N) •
        (fun ω => ENNReal.ofReal (bandNormalizedConfigurationDensity μ S r ω))) :=
      (withDensity_smul' _ _ (by simp)).symm
    _ = (fiberLaw μ N).withDensity (ENNReal.ofReal (poissonWeight μ.mass N) •
        (fun ω => ENNReal.ofReal (bandPoissonLikelihood μ S r ω))) := withDensity_congr_ae hENN
    _ = ENNReal.ofReal (poissonWeight μ.mass N) • (fiberLaw μ N).withDensity
        (fun ω => ENNReal.ofReal (bandPoissonLikelihood μ S r ω)) := withDensity_smul' _ _ (by simp)
    _ = _ := (withDensity_smul_measure _ _).symm

/-- The complete finite Poisson configuration has its actual band likelihood.
No count or label is supplied to a policy by this measure identity. -/
theorem configurationLaw_bandScaled_withDensity (μ : FiniteMeasure ℝ) {S : Set ℝ}
    (hS : MeasurableSet S) {r : ℝ≥0} (hr : 0 < r) :
    configurationLaw (bandScaledIntensity μ S r)=(configurationLaw μ).withDensity
      (fun ω => ENNReal.ofReal (bandPoissonLikelihood μ S r ω)) := by
  by_cases hμ : μ=0
  · subst μ
    have hZero : bandScaledIntensity 0 S r=0 := by
      apply FiniteMeasure.toMeasure_injective
      rw [bandScaledIntensity_toMeasure 0 hS r]
      simp
    simp only [hZero,configurationLaw_zero]
    have hDensity : Measurable (fun ω => ENNReal.ofReal (bandPoissonLikelihood 0 S r ω)) :=
      ENNReal.measurable_ofReal.comp (measurable_bandPoissonLikelihood 0 hS r)
    rw [dirac_withDensity' hDensity]
    simp [bandPoissonLikelihood,hZero,pointCount,emptyConfiguration,configurationMk]
  · unfold configurationLaw
    rw [withDensity_sum]
    apply congrArg Measure.sum
    funext N
    exact poissonFiber_bandScale_likelihood μ hS hr hμ N

end ProphetSecretary.Limiting
