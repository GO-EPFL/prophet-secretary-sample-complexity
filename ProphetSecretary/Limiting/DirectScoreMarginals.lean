import ProphetSecretary.Limiting.FinitePoissonApproximation
import ProphetSecretary.Limiting.HybridPositivePairs
import ProphetSecretary.Probability.BandScore

/-!
# Marginal calibration for direct finite Poisson scores

The virtual law is a zero-inflated normalized intensity. Positive-band mass
is exactly intensity divided by the fixed number of virtual variables. The
zero atom has mass at least one minus the mixture probability, including
zero intensity and the normalization fallback at zero.
-/
open MeasureTheory Set
open scoped Classical NNReal
namespace ProphetSecretary.Limiting

lemma zeroInflatedLaw_real (κ : Measure ℝ) [IsProbabilityMeasure κ] (p : unitInterval)
    {S : Set ℝ} (hS : MeasurableSet S) :
    (zeroInflatedLaw κ p).real S=(1-(p:ℝ))*S.indicator (fun _ => (1:ℝ)) 0+(p:ℝ)*κ.real S := by
  calc
    _ = ∫ x, S.indicator (fun _ : ℝ => (1:ℝ)) x ∂zeroInflatedLaw κ p := (integral_indicator_one hS).symm
    _ = (1-(p:ℝ))*S.indicator (fun _ => (1:ℝ)) 0+(p:ℝ)*∫ x, S.indicator (fun _ : ℝ => (1:ℝ)) x ∂κ :=
      integral_zeroInflatedLaw κ p ((integrable_const 1).indicator hS)
    _ = _ := congrArg (fun z : ℝ => (1-(p:ℝ))*S.indicator (fun _ => (1:ℝ)) 0+(p:ℝ)*z)
      (integral_indicator_one (μ := κ) hS)

lemma zeroInflatedLaw_real_of_notMem_zero (κ : Measure ℝ) [IsProbabilityMeasure κ] (p : unitInterval)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S) :
    (zeroInflatedLaw κ p).real S=(p:ℝ)*κ.real S := by
  rw [zeroInflatedLaw_real κ p hS,indicator_of_notMem hS0,mul_zero,zero_add]

lemma zeroInflatedLaw_zero_mass_ge (κ : Measure ℝ) [IsProbabilityMeasure κ] (p : unitInterval) :
    1-(p:ℝ)≤(zeroInflatedLaw κ p).real {0} := by
  rw [zeroInflatedLaw_real κ p (measurableSet_singleton 0)]
  simpa using le_add_of_nonneg_right (a := 1-(p:ℝ)) (mul_nonneg p.property.1 (measureReal_nonneg : 0≤κ.real {0}))

lemma normalizedMarkOrZero_mass_mul_real (μ : FiniteMeasure ℝ) (S : Set ℝ) :
    (μ.mass:ℝ)*(normalizedMarkOrZero μ).real S=(μ:Measure ℝ).real S := by
  by_cases hμ : μ=0
  · subst μ
    change (0:ℝ)*(normalizedMarkOrZero 0).real S=(0:Measure ℝ).real S
    simp only [zero_mul,measureReal_zero,Pi.zero_apply]
  · rw [normalizedMarkOrZero,if_neg hμ]
    exact mass_mul_normalize_measureReal μ S

lemma directPoissonMarginal_band_mass (μ : FiniteMeasure ℝ) (p : unitInterval) (N : ℕ)
    (hp : (p:ℝ)=(μ.mass:ℝ)/(N:ℝ)) {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S) :
    (zeroInflatedLaw (normalizedMarkOrZero μ) p).real S=(μ:Measure ℝ).real S/(N:ℝ) := by
  rw [zeroInflatedLaw_real_of_notMem_zero _ p hS hS0,hp]
  calc
    _ = ((μ.mass:ℝ)*(normalizedMarkOrZero μ).real S)/(N:ℝ) := by ring
    _ = _ := by rw [normalizedMarkOrZero_mass_mul_real]

lemma directPoissonMarginal_zero_mass_ge_half (μ : FiniteMeasure ℝ) (p : unitInterval)
    (hp : (p:ℝ)≤1/2) : (1/2:ℝ)≤(zeroInflatedLaw (normalizedMarkOrZero μ) p).real {0} := by
  exact (show (1/2:ℝ)≤1-(p:ℝ) by linarith only [hp]).trans (zeroInflatedLaw_zero_mass_ge _ p)
end ProphetSecretary.Limiting
