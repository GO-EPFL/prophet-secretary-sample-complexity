import ProphetSecretary.Limiting.HybridIntensityBenchmark
import ProphetSecretary.Limiting.IntensityMassConvergence

/-!
# Growing-prefix benchmark errors under ordered intensity convergence

Only the common cap is used; the number of retained variables may vary.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal

namespace ProphetSecretary.Limiting

theorem hybrid_intensity_benchmark_difference_tendsto {Γ : Type*} {l : Filter Γ}
    (sizes : Γ → ℕ) (Bs Ds : ∀ m, FiniteIntensityHybridInstance (sizes m))
    (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hCap : ∀ m, (Bs m).cap ≤ H) (hOrderCap : ∀ m, (Ds m).cap ≤ (Bs m).cap)
    (hTerm : ∀ m, (Ds m).terminal = (Bs m).terminal)
    (hP : ∀ m, (Ds m).individuals = (Bs m).individuals)
    (hBase : ∀ m, (Bs m).intensity = μ)
    (hOrder : ∀ m, (μ : Measure ℝ) ≤ ((Ds m).intensity : Measure ℝ))
    (hWeak : Tendsto (fun m => (Ds m).intensity) l (𝓝 μ)) :
    Tendsto (fun m => (Ds m).expectedMaximum-(Bs m).expectedMaximum) l (𝓝 (0 : ℝ)) := by
  have hMass := finiteIntensityDifference_real_mass_tendsto (fun m => (Ds m).intensity) μ hOrder hWeak
  have hLimit := hMass.const_mul (H : ℝ)
  simp only [mul_zero] at hLimit
  apply squeeze_zero' _ _ hLimit
  · filter_upwards [] with m
    have ho : ((Bs m).intensity : Measure ℝ) ≤ ((Ds m).intensity : Measure ℝ) := by
      rw [hBase m]
      exact hOrder m
    exact ((Bs m).expectedMaximum_intensity_order (Ds m) (hOrderCap m) (hTerm m) (hP m) ho).1
  · filter_upwards [] with m
    have ho : ((Bs m).intensity : Measure ℝ) ≤ ((Ds m).intensity : Measure ℝ) := by
      rw [hBase m]
      exact hOrder m
    have h := ((Bs m).expectedMaximum_intensity_order (Ds m) (hOrderCap m) (hTerm m) (hP m) ho).2
    rw [hBase m] at h
    exact h.trans (mul_le_mul_of_nonneg_right (show ((Bs m).cap : ℝ) ≤ H by exact_mod_cast hCap m) measureReal_nonneg)

end ProphetSecretary.Limiting
