import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Metrizable
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Measurability of a linear response

Measurable fixed-parameter payoffs and a uniform quadratic Taylor remainder make
the response a pointwise limit of measurable difference quotients. Joint
measurability in the perturbation parameter is not required. This supplies the
data-dependent derivative measurability needed in `thm:bayes`.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

theorem measurable_linearResponse {Ω : Type*} [MeasurableSpace Ω]
    (f : ℝ → Ω → ℝ) (D : Ω → ℝ) {C ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ θ ∈ Icc (0 : ℝ) ρ, Measurable (f θ))
    (hTaylor : ∀ d θ, θ ∈ Icc (0 : ℝ) ρ →
      |f θ d - f 0 d - θ * D d| ≤ C * θ ^ 2) : Measurable D := by
  let step : ℕ → ℝ := fun m => ρ / ((m : ℝ) + 1)
  have hstepPos (m : ℕ) : 0 < step m := div_pos hρ (by positivity)
  have hstepLe (m : ℕ) : step m ≤ ρ := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (m : ℝ) + 1)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hstepLim : Tendsto step atTop (𝓝 (0 : ℝ)) := by
    simpa only [step, div_eq_mul_inv, one_div, one_mul, mul_zero] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ρ
  let quotient : ℕ → Ω → ℝ := fun m d => (f (step m) d - f 0 d) / step m
  have hquotientMeas (m : ℕ) : Measurable (quotient m) :=
    ((hf (step m) ⟨(hstepPos m).le, hstepLe m⟩).sub (hf 0 ⟨le_rfl, hρ.le⟩)).div_const (step m)
  have hquotientLim (d : Ω) : Tendsto (fun m => quotient m d) atTop (𝓝 (D d)) := by
    have herror (m : ℕ) : |quotient m d - D d| ≤ C * step m := by
      have ht := hTaylor d (step m) ⟨(hstepPos m).le, hstepLe m⟩
      have heq : quotient m d - D d =
          (f (step m) d - f 0 d - step m * D d) / step m := by
        dsimp [quotient]
        field_simp [(hstepPos m).ne']
      rw [heq, abs_div, abs_of_pos (hstepPos m)]
      apply (div_le_iff₀ (hstepPos m)).mpr
      simpa only [pow_two, mul_assoc] using ht
    have hboundLim : Tendsto (fun m => C * step m) atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using hstepLim.const_mul C
    apply Metric.tendsto_nhds.mpr
    intro ε hε
    filter_upwards [(tendsto_order.mp hboundLim).2 ε hε] with m hm
    rw [Real.dist_eq]
    exact (herror m).trans_lt hm
  exact measurable_of_tendsto_metrizable hquotientMeas (tendsto_pi_nhds.mpr hquotientLim)

end ProphetSecretary.Analysis
