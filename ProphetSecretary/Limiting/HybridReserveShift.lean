import ProphetSecretary.Limiting.HybridReserveBounds
import ProphetSecretary.Limiting.FinitePoissonApproximation
import ProphetSecretary.Limiting.HybridTerminalZeroIntensity

/-!
# Exact scalar reserve removal in the finite-intensity hybrid model

Finite Bernoulli potentials bound every original-history competing rule and
supply explicit admissible lower-comparison rules. Their value/error limits
prove the equality. No convergence or existence of an optimizing hybrid policy
is inferred from scalar-value convergence.
-/

open MeasureTheory Set Filter
open scoped Topology Classical NNReal

namespace ProphetSecretary.Limiting

variable {n : ℕ}

/-- A fixed terminal reward contributes wa plus the optimal excess-state value.
Original retained zero identities and all original anonymous observations are
permitted in the competing-policy upper comparison. -/
theorem FiniteIntensityHybridInstance.value_reserveShift (B : FiniteIntensityHybridInstance n)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c = w * (B.terminal : ℝ) + (B.excessState B.terminal).optimalScalarValue w c := by
  by_cases hμ : B.intensity = 0
  · exact B.value_reserveShift_zeroIntensity hμ hw hc
  · let S := B.excessState B.terminal
    let rate := (S.intensity : Measure ℝ).real univ
    have hrate : 0 ≤ rate := measureReal_nonneg
    let K := fun j : ℕ => bernoulliMultiplicity rate j
    let p := fun j : ℕ => bernoulliProbability rate hrate j
    let κ := normalizedMarkOrZero S.intensity
    let M := ∫ x, x ∂κ
    let C := fun j : ℕ => (Real.pi / 2) * w * M * Real.sqrt ((K j : ℝ) * (p j : ℝ) ^ 2)
    let E := fun j : ℕ => (K j : ℝ) * (w * (p j : ℝ) ^ 2 * M) + C j
    have hV := S.finitePoissonApproximation_value_tendsto (by rfl) hw hc
    have hC : Tendsto C atTop (𝓝 0) := by
      have hs := bernoulliProbability_squareSum_tendsto_zero rate hrate
      have h := (Real.continuous_sqrt.tendsto 0 |>.comp hs).const_mul ((Real.pi / 2) * w * M)
      simpa only [Function.comp_apply,Real.sqrt_zero,mul_zero] using h
    have hE : Tendsto E atTop (𝓝 0) := bernoulliProbability_error_tendsto_zero rate hrate w M
    have hU (j : ℕ) : B.optimalScalarValue w c ≤
        w * (B.terminal : ℝ) + Model.optimalScalarValue (S.finitePoissonApproximation j) w c + C j :=
      B.value_le_reserveBernoulliDesign (k := K j) hμ (p j) (bernoulliProbability_total rate hrate j).symm hw hc
    have hL (j : ℕ) : w * (B.terminal : ℝ) + Model.optimalScalarValue (S.finitePoissonApproximation j) w c ≤
        B.optimalScalarValue w c + E j := by
      have h := B.reserveBernoulliDesign_le_value (k := K j) hμ (p j)
        (bernoulliProbability_total rate hrate j).symm hw hc
      change w * (B.terminal : ℝ) + Model.optimalScalarValue (S.finitePoissonApproximation j) w c ≤
        B.optimalScalarValue w c + (K j : ℝ) * (w * (p j : ℝ) ^ 2 * M) + C j at h
      exact h.trans_eq (by dsimp only [E]; ring)
    have hULim : Tendsto (fun j => w * (B.terminal : ℝ) + Model.optimalScalarValue (S.finitePoissonApproximation j) w c + C j)
        atTop (𝓝 (w * (B.terminal : ℝ) + S.optimalScalarValue w c)) := by
      simpa only [add_zero] using (hV.const_add (w * (B.terminal : ℝ))).add hC
    have hLLim := hV.const_add (w * (B.terminal : ℝ))
    have hRLim : Tendsto (fun j => B.optimalScalarValue w c + E j) atTop (𝓝 (B.optimalScalarValue w c)) := by
      simpa only [add_zero] using hE.const_add (B.optimalScalarValue w c)
    exact le_antisymm (le_of_tendsto_of_tendsto tendsto_const_nhds hULim (Filter.Eventually.of_forall hU))
      (le_of_tendsto_of_tendsto hLLim hRLim (Filter.Eventually.of_forall hL))

end ProphetSecretary.Limiting
