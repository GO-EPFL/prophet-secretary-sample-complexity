import ProphetSecretary.Limiting.HybridIntensityComparison
import ProphetSecretary.Limiting.BoundedIntensityMoment

/-!
# Residual-intensity errors uniform in retained dimension

The retained prefix may grow while an ordered intensity converges weakly.
First-moment convergence and the dimension-free intensity comparison give one
error bound for every bounded reward weight and all duration weights.
-/

open MeasureTheory Set Filter
open scoped Topology Classical NNReal

namespace ProphetSecretary.Limiting

theorem hybrid_intensity_uniform_error {Γ : Type*} {l : Filter Γ}
    (sizes : Γ → ℕ) (Bs Ds : ∀ m, FiniteIntensityHybridInstance (sizes m))
    (μ : FiniteMeasure ℝ) (H W : ℝ≥0)
    (hCap : ∀ m, (Ds m).cap ≤ H)
    (hOrderCap : ∀ m, (Ds m).cap ≤ (Bs m).cap)
    (hTerm : ∀ m, (Ds m).terminal = (Bs m).terminal)
    (hP : ∀ m, (Ds m).individuals = (Bs m).individuals)
    (hBase : ∀ m, (Bs m).intensity = μ)
    (hμCap : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H)
    (hOrder : ∀ m, (μ : Measure ℝ) ≤ ((Ds m).intensity : Measure ℝ))
    (hWeak : Tendsto (fun m => (Ds m).intensity) l (𝓝 μ)) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in l, ∀ w c : ℝ, 0 ≤ w → w ≤ W → 0 ≤ c →
      |(Ds m).optimalScalarValue w c-(Bs m).optimalScalarValue w c| < ε := by
  have hsCap (m : Γ) : ∀ᵐ x ∂((Ds m).intensity : Measure ℝ), x ∈ Icc (0 : ℝ) H :=
    (Ds m).intensity_supported.mono (fun _ hx => ⟨hx.1.le,hx.2.trans (by exact_mod_cast hCap m)⟩)
  have hMoment := finiteIntensity_difference_firstMoment_tendsto (fun m => (Ds m).intensity) μ H
    hsCap hμCap hOrder hWeak
  intro ε hε
  have hεW : 0 < ε/((W : ℝ)+1) := div_pos hε (by positivity)
  have hSmall := (tendsto_order.mp hMoment).2 _ hεW
  filter_upwards [hSmall] with m hm
  intro w c hw hwW hc
  have hOrder' : ((Bs m).intensity : Measure ℝ) ≤ ((Ds m).intensity : Measure ℝ) := by
    rw [hBase m]
    exact hOrder m
  have hV := (Bs m).value_intensity_mono_lipschitz (Ds m) (hOrderCap m) (hTerm m) (hP m) hOrder' hw hc
  rw [hBase m] at hV
  have hn : 0 ≤ ∫ x, x ∂(((Ds m).intensity : Measure ℝ)-(μ : Measure ℝ)) := by
    apply integral_nonneg_of_ae
    have hs : ∀ᵐ x ∂(((Ds m).intensity : Measure ℝ)-(μ : Measure ℝ)), x ∈ Icc (0 : ℝ) H :=
      ae_mono Measure.sub_le (hsCap m)
    exact hs.mono (fun _ hx => hx.1)
  rw [abs_of_nonneg hV.1]
  have hwδ := mul_le_mul_of_nonneg_right hwW hn
  have hBound : w*(∫ x, x ∂(((Ds m).intensity : Measure ℝ)-(μ : Measure ℝ))) < ε := by
    have h := mul_lt_mul_of_pos_left hm (by positivity : 0 < (W : ℝ)+1)
    have hEq : ((W : ℝ)+1)*(ε/((W : ℝ)+1)) = ε := by field_simp
    rw [hEq] at h
    nlinarith only [hwδ,h,hn]
  exact hV.2.trans_lt hBound

end ProphetSecretary.Limiting
