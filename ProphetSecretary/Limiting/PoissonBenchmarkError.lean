import ProphetSecretary.Limiting.PoissonBenchmarkComparison
import ProphetSecretary.Probability.BoundedCDFComparison

/-!
# Explicit benchmark error in finite causal Poisson replacement

This proves a separate prophet-maximum comparison by actual CDFs and layer
cake. It is not inferred from convergence of stopping values.
-/

open MeasureTheory Set
open scoped BigOperators Classical NNReal

namespace ProphetSecretary.Limiting

open ProphetSecretary.Probability

variable {n m : ℕ}

theorem finite_poisson_benchmark_comparison (P : Model.Instance n) (R : Model.Instance m)
    (H : ℝ≥0) (hP : ∀ i, ∀ᵐ x ∂P.law i, x ≤ (H : ℝ))
    (hR : ∀ i, ∀ᵐ x ∂R.law i, x ≤ (H : ℝ)) :
    let B := poissonizedFamily P R H hP hR
    0 ≤ (P.appendIndependent R).expectedMaximum-B.expectedMaximum ∧
      (P.appendIndependent R).expectedMaximum-B.expectedMaximum ≤
        (H : ℝ)*(∑ i, ((R.law i).real (Ioi (0 : ℝ)))^2) := by
  let S := P.appendIndependent R
  let B := poissonizedFamily P R H hP hR
  have hS : ∀ᵐ x ∂S.valuesLaw, Model.Instance.maximum x ∈ Icc (0 : ℝ) H := by
    have hValues : ∀ᵐ x ∂S.valuesLaw, ∀ i, x i ≤ (H : ℝ) := by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval S.law i).quasiMeasurePreserving.ae
        (P.appendIndependent_bounded R hP hR i)
    exact hValues.mono (fun x hx => ⟨Model.Instance.maximum_nonnegative x,
      Model.Instance.maximum_le x H.property hx⟩)
  have hB : ∀ᵐ v ∂hybridValueLaw P B.intensity, hybridMaximum 0 v ∈ Icc (0 : ℝ) H := by
    filter_upwards [hybridValueLaw_values_bounds P B.intensity hP B.intensity_supported] with v hv
    exact ⟨hybridMaximum_nonnegative _ _,hybridMaximum_le H.property H.property v (fun i => (hv i).2)⟩
  have hCDF : ∀ t ∈ Ioc (0 : ℝ) H,
      0 ≤ (hybridValueLaw P B.intensity).real {v | hybridMaximum 0 v ≤ t}-
        S.valuesLaw.real {x | Model.Instance.maximum x ≤ t} ∧
      (hybridValueLaw P B.intensity).real {v | hybridMaximum 0 v ≤ t}-
        S.valuesLaw.real {x | Model.Instance.maximum x ≤ t} ≤
          ∑ i, ((R.law i).real (Ioi (0 : ℝ)))^2 := by
    intro t ht
    have h := finite_poisson_maximum_cdf_comparison P R H hP hR ht.1.le
    refine ⟨h.1,h.2.trans ?_⟩
    apply Finset.sum_le_sum
    intro i _
    apply (sq_le_sq₀ measureReal_nonneg measureReal_nonneg).mpr
    exact measureReal_mono (Ioi_subset_Ioi ht.1.le)
  have h := bounded_integral_sub_le_of_cdf S.valuesLaw (hybridValueLaw P B.intensity)
    Model.Instance.maximum (hybridMaximum 0) Model.Instance.measurable_maximum
    (measurable_hybridMaximum 0) H (∑ i, ((R.law i).real (Ioi (0 : ℝ)))^2) hS hB hCDF
  exact h

end ProphetSecretary.Limiting
