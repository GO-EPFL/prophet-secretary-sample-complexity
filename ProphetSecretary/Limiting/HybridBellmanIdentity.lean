import ProphetSecretary.Limiting.BernoulliExpectedLossError
import ProphetSecretary.Limiting.BernoulliResidualError
import ProphetSecretary.Limiting.HybridValuePolicyZeroIntensity

/-!
# Actual hybrid Bellman identity and value-threshold verification

A single arbitrary competing policy is fixed before the finite virtual count
tends to infinity. The proved actual zero-augmentation transports its payoff
exactly; finite-design action losses converge to its actual continuation loss,
and the signed generator error vanishes. Thus value-threshold optimality is
verified against the full admissible class, rather than assumed or inferred
from convergence of optimized values alone.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

/-- The nonzero-intensity branch of the actual all-policy performance identity.
The zero-intensity optimizer boundary is separately proved by finite simulation. -/
theorem RandomizedHybridPolicy.actual_bellmanIdentity_of_nonzero_intensity
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (hμ : B.intensity ≠ 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    B.optimalScalarValue w c-π.scalarObjective B w c = π.expectedValueLoss B w c := by
  let qs := fun j => bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j
  let Qs := fun j => B.bernoulliApproximation hμ j
  let Ts := fun j => B.appendZeroIndividuals (qs j)
  let σ := fun j => π.ignoreIndividualExtras (qs j)
  have hQ (j : ℕ) : Integrable Model.Instance.maximum (Qs j).valuesLaw :=
    finitePoissonDesign_integrable_maximum B.individuals _ _ _ _
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) (B.normalizedMark_integrable hμ)
  have hValue : Tendsto (fun j => Model.optimalScalarValue (Qs j) w c) atTop (𝓝 (B.optimalScalarValue w c)) :=
    B.bernoulliApproximation_value_tendsto ha hμ hw hc
  have hLoss : Tendsto (fun j => (σ j).expectedDesignActionLoss (Qs j) (Ts j) w c)
      atTop (𝓝 (π.expectedValueLoss B w c)) := by
    have hRate : Tendsto (fun j => ((n : ℝ)+(B.intensity.mass : ℝ))*B.bernoulliClockErrorBound w j)
        atTop (𝓝 (0 : ℝ)) := by
      simpa only [mul_zero] using (B.bernoulliClockErrorBound_tendsto_zero w).const_mul ((n : ℝ)+(B.intensity.mass : ℝ))
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ hRate
    intro j
    simpa only [Real.norm_eq_abs] using π.bernoulli_expectedDesignLoss_error B ha hμ j hw hc
  have hResidual : Tendsto (fun j => (σ j).expectedDesignResidual (Qs j) (Ts j) hμ w c) atTop (𝓝 (0 : ℝ)) := by
    apply tendsto_iff_norm_sub_tendsto_zero.mpr
    apply squeeze_zero (fun _ => norm_nonneg _) _ (B.bernoulliStateError_tendsto_zero w)
    intro j
    simpa only [Real.norm_eq_abs,sub_zero] using B.bernoulli_expectedDesignResidual_abs_le hμ j (σ j) hw hc
  have hIdentity (j : ℕ) : Model.optimalScalarValue (Qs j) w c-π.scalarObjective B w c =
      (σ j).expectedDesignResidual (Qs j) (Ts j) hμ w c+(σ j).expectedDesignActionLoss (Qs j) (Ts j) w c := by
    have h := (σ j).finiteDesign_residualIdentity_split (Qs j) (hQ j) (Ts j) ha hμ hw hc
    have hScalar : (σ j).scalarObjective (Ts j) w c = π.scalarObjective B w c :=
      π.scalarObjective_ignoreIndividualExtras B (qs j) ha w c
    rw [hScalar] at h
    exact h
  have hLeft := hValue.sub_const (π.scalarObjective B w c)
  have hRight := hResidual.add hLoss
  have hRight' : Tendsto (fun j => Model.optimalScalarValue (Qs j) w c-π.scalarObjective B w c)
      atTop (𝓝 (0+π.expectedValueLoss B w c)) :=
    Tendsto.congr' (Eventually.of_forall fun j => (hIdentity j).symm) hRight
  simpa only [zero_add] using tendsto_nhds_unique hLeft hRight'

/-- The actual measurable threshold policy attains the unrestricted hybrid
supremum. Zero intensity, empty retained sets and zero mean are included;
positive reward weight and nonnegative duration weight are explicit. -/
theorem FiniteIntensityHybridInstance.valueThresholdPolicy_optimal
    (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (B.valueThresholdPolicy hw.le hc).scalarObjective B w c = B.optimalScalarValue w c := by
  by_cases hμ : B.intensity = 0
  · exact B.valueThresholdPolicy_optimal_zero_intensity ha hμ hw hc
  · have h := (B.valueThresholdPolicy hw.le hc).actual_bellmanIdentity_of_nonzero_intensity B ha hμ hw hc
    rw [B.valueThresholdPolicy_expectedValueLoss_zero hw hc] at h
    linarith

end ProphetSecretary.Limiting
