import ProphetSecretary.Limiting.ExcessIntensity
import ProphetSecretary.Limiting.FiniteBernoulliApproximation
import ProphetSecretary.Limiting.ZeroIntensity

/-!
# Finite Poisson approximation including zero total intensity

The analytical zero-rate mark law is chosen as δ₀, so every design law is
nonnegative even when ordinary normalization has an arbitrary fallback. The
actual zero-intensity hybrid process remains empty. Value convergence follows
from the proved nonzero-intensity approximation and exact zero simulation.
-/

open MeasureTheory Set Filter
open scoped Topology NNReal Classical

namespace ProphetSecretary.Limiting

variable {n : ℕ}

lemma finitePoissonDesign_probability_zero (P : Model.Instance n) (κ : Measure ℝ) [IsProbabilityMeasure κ]
    (hκ : ∀ᵐ x ∂κ, 0 ≤ x) (k : ℕ) : finitePoissonDesign P κ hκ 0 k = P.appendZeros k := by
  apply Model.Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases with
  | left i => simp only [finitePoissonDesign,appendIID,Model.Instance.appendZeros,Fin.addCases_left]
  | right j => simp [finitePoissonDesign,appendIID,Model.Instance.appendZeros,zeroInflatedLaw,Model.jackpotLaw]

noncomputable def FiniteIntensityHybridInstance.finitePoissonApproximation (B : FiniteIntensityHybridInstance n) (m : ℕ) :
    Model.Instance (n + bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) m) :=
  finitePoissonDesign B.individuals (normalizedMarkOrZero B.intensity)
    ((normalizedMarkOrZero_bounds B.intensity B.cap.property B.intensity_supported).mono (fun _ hx => hx.1))
      (bernoulliProbability ((B.intensity : Measure ℝ).real univ) measureReal_nonneg m)
        (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) m)

theorem FiniteIntensityHybridInstance.finitePoissonApproximation_value_tendsto (B : FiniteIntensityHybridInstance n)
    (ha : B.terminal = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    Tendsto (fun m => Model.optimalScalarValue (B.finitePoissonApproximation m) w c)
      atTop (𝓝 (B.optimalScalarValue w c)) := by
  by_cases hμ : B.intensity = 0
  · have hr : (B.intensity : Measure ℝ).real univ = 0 := by rw [hμ]; simp [Measure.real]
    have he (m : ℕ) : B.finitePoissonApproximation m = B.individuals.appendZeros
        (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) m) := by
      have hp : bernoulliProbability ((B.intensity : Measure ℝ).real univ) measureReal_nonneg m = 0 := by
        apply Subtype.ext
        change ((B.intensity : Measure ℝ).real univ) /
          (bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) m : ℝ) = 0
        rw [hr,zero_div]
      unfold FiniteIntensityHybridInstance.finitePoissonApproximation
      rw [hp,finitePoissonDesign_probability_zero]
    have hv (m : ℕ) : Model.optimalScalarValue (B.finitePoissonApproximation m) w c = B.optimalScalarValue w c := by
      rw [he m,B.individuals.optimalScalarValue_appendZeros _
        (B.individuals.integrable_maximum_of_bounded B.individual_bounded) hw.le hc,B.value_zero_intensity ha hμ hw.le hc]
    have hfun : (fun m => Model.optimalScalarValue (B.finitePoissonApproximation m) w c) =
        fun _ : ℕ => B.optimalScalarValue w c := funext hv
    rw [hfun]
    exact tendsto_const_nhds
  · have hk : normalizedMarkOrZero B.intensity = (B.intensity.normalize : Measure ℝ) := by
      rw [normalizedMarkOrZero,if_neg hμ]
    have he (m : ℕ) : B.finitePoissonApproximation m = B.bernoulliApproximation hμ m := by
      apply Model.Instance.eq_of_law_eq
      funext i
      induction i using Fin.addCases with
      | left i => simp only [FiniteIntensityHybridInstance.finitePoissonApproximation,
          FiniteIntensityHybridInstance.bernoulliApproximation,finitePoissonDesign,appendIID,Fin.addCases_left]
      | right j =>
        simp only [FiniteIntensityHybridInstance.finitePoissonApproximation,
          FiniteIntensityHybridInstance.bernoulliApproximation,finitePoissonDesign,appendIID,Fin.addCases_right]
        exact congrArg (fun κ : Measure ℝ => zeroInflatedLaw κ (bernoulliProbability ((B.intensity : Measure ℝ).real univ) measureReal_nonneg m)) hk
    have hfun : (fun m => Model.optimalScalarValue (B.finitePoissonApproximation m) w c) =
        fun m => Model.optimalScalarValue (B.bernoulliApproximation hμ m) w c := by
      funext m
      rw [he m]
    rw [hfun]
    exact B.bernoulliApproximation_value_tendsto ha hμ hw hc

end ProphetSecretary.Limiting
