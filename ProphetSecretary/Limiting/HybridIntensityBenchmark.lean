import ProphetSecretary.Limiting.HybridIntensityCDFOrder
import ProphetSecretary.Probability.BoundedCDFComparison

/-!
# Benchmark errors for ordered finite intensities

The upper bound is the cap times the total added intensity. Its constant is
independent of the number of retained variables, which may grow in extraction.
-/

open MeasureTheory Set
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

theorem FiniteIntensityHybridInstance.expectedMaximum_intensity_order
    (B D : FiniteIntensityHybridInstance n) (hCap : D.cap ≤ B.cap)
    (hTerm : D.terminal = B.terminal) (hP : D.individuals = B.individuals)
    (hOrder : (B.intensity : Measure ℝ) ≤ (D.intensity : Measure ℝ)) :
    0 ≤ D.expectedMaximum-B.expectedMaximum ∧
      D.expectedMaximum-B.expectedMaximum ≤
        (B.cap : ℝ)*(finiteIntensityDifference D.intensity B.intensity : Measure ℝ).real univ := by
  have hB : ∀ᵐ v ∂hybridValueLaw B.individuals B.intensity,
      hybridMaximum B.terminal v ∈ Icc (0 : ℝ) B.cap := by
    filter_upwards [hybridValueLaw_values_bounds B.individuals B.intensity B.individual_bounded B.intensity_supported] with v hv
    exact ⟨hybridMaximum_nonnegative _ _,hybridMaximum_le B.cap.property B.terminal_le_cap_real v (fun i => (hv i).2)⟩
  have hD : ∀ᵐ v ∂hybridValueLaw D.individuals D.intensity,
      hybridMaximum D.terminal v ∈ Icc (0 : ℝ) B.cap := by
    filter_upwards [hybridValueLaw_values_bounds D.individuals D.intensity D.individual_bounded D.intensity_supported] with v hv
    exact ⟨hybridMaximum_nonnegative _ _,(hybridMaximum_le D.cap.property D.terminal_le_cap_real v
      (fun i => (hv i).2)).trans (by exact_mod_cast hCap)⟩
  have hCDF : ∀ t ∈ Ioc (0 : ℝ) B.cap,
      0 ≤ (hybridValueLaw B.individuals B.intensity).real {v | hybridMaximum B.terminal v ≤ t}-
        (hybridValueLaw D.individuals D.intensity).real {v | hybridMaximum D.terminal v ≤ t} ∧
      (hybridValueLaw B.individuals B.intensity).real {v | hybridMaximum B.terminal v ≤ t}-
        (hybridValueLaw D.individuals D.intensity).real {v | hybridMaximum D.terminal v ≤ t} ≤
          (finiteIntensityDifference D.intensity B.intensity : Measure ℝ).real univ := by
    intro t _
    by_cases hat : (B.terminal : ℝ) ≤ t
    · have h := hybrid_maximum_cdf_intensity_order B.individuals B.intensity D.intensity hOrder B.terminal hat
      simpa only [hP,hTerm] using h
    · have hDb : t < (D.terminal : ℝ) := by rw [hTerm]; exact not_le.mp hat
      rw [hybridMaximum_real_Iic_below B.individuals B.intensity (not_le.mp hat),
        hybridMaximum_real_Iic_below D.individuals D.intensity hDb]
      simp only [sub_self,le_refl,true_and]
      exact measureReal_nonneg
  exact ProphetSecretary.Probability.bounded_integral_sub_le_of_cdf
    (hybridValueLaw D.individuals D.intensity) (hybridValueLaw B.individuals B.intensity)
    (hybridMaximum D.terminal) (hybridMaximum B.terminal)
    (measurable_hybridMaximum _) (measurable_hybridMaximum _) B.cap
    ((finiteIntensityDifference D.intensity B.intensity : Measure ℝ).real univ) hD hB hCDF

end ProphetSecretary.Limiting
