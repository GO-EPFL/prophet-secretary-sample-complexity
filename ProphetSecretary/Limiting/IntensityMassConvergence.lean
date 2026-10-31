import ProphetSecretary.Limiting.ExcessIntensityOrder

/-!
# Vanishing added mass under ordered finite-intensity weak convergence

The difference is the actual positive measure ν−μ. Its mass is obtained from
the exact additive measure identity and continuity of finite-measure mass.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Limiting

lemma finiteIntensityDifference_real_mass (ν μ : FiniteMeasure ℝ)
    (hOrder : (μ : Measure ℝ) ≤ (ν : Measure ℝ)) :
    (finiteIntensityDifference ν μ : Measure ℝ).real univ = (ν.mass : ℝ)-(μ.mass : ℝ) := by
  have he := congrArg (fun κ : FiniteMeasure ℝ => (κ : Measure ℝ).real univ)
    (add_finiteIntensityDifference ν μ hOrder)
  change ((μ : Measure ℝ)+(finiteIntensityDifference ν μ : Measure ℝ)).real univ = (ν : Measure ℝ).real univ at he
  rw [measureReal_add_apply] at he
  change (μ.mass : ℝ)+(finiteIntensityDifference ν μ : Measure ℝ).real univ = (ν.mass : ℝ) at he
  linarith only [he]

theorem finiteIntensityDifference_real_mass_tendsto {Γ : Type*} {l : Filter Γ}
    (νs : Γ → FiniteMeasure ℝ) (μ : FiniteMeasure ℝ)
    (hOrder : ∀ m, (μ : Measure ℝ) ≤ (νs m : Measure ℝ))
    (hWeak : Tendsto νs l (𝓝 μ)) :
    Tendsto (fun m => (finiteIntensityDifference (νs m) μ : Measure ℝ).real univ) l (𝓝 (0 : ℝ)) := by
  have hm := (NNReal.continuous_coe.tendsto μ.mass).comp hWeak.mass
  have h := hm.sub_const (μ.mass : ℝ)
  simp only [sub_self] at h
  have he : (fun m => (finiteIntensityDifference (νs m) μ : Measure ℝ).real univ) =
      (fun m => ((νs m).mass : ℝ)-(μ.mass : ℝ)) :=
    funext (fun m => finiteIntensityDifference_real_mass (νs m) μ (hOrder m))
  rwa [he]

end ProphetSecretary.Limiting
