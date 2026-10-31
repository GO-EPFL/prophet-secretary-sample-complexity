import ProphetSecretary.Limiting.MappedReserveGeneratorError
import ProphetSecretary.Limiting.MappedPotentialIdentity
import ProphetSecretary.Limiting.HybridMappedZero

/-!
# Two-sided reserve comparisons through finite Bernoulli potentials

All original-history competing policies satisfy the upper comparison. A shared
positive-excess threshold rule, followed by the constructed independent virtual
zero simulation, supplies the lower comparison. Every finite-stage policy is
admissible before taking the value limit; policy convergence is not assumed.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal

namespace ProphetSecretary.Limiting

variable {n k : ℕ}

theorem FiniteIntensityHybridInstance.value_le_reserveBernoulliDesign (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity ≠ 0) (p : unitInterval)
    (hrate : ((B.excessState B.terminal).intensity : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let S := B.excessState B.terminal
    let κ := normalizedMarkOrZero S.intensity
    let hκ := (B.excessState_markBounds B.terminal).mono (fun _ hx => hx.1)
    let Q := finitePoissonDesign S.individuals κ hκ p k
    let C := (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2)
    B.optimalScalarValue w c ≤ w * (B.terminal : ℝ) + Model.optimalScalarValue Q w c + C := by
  let S := B.excessState B.terminal
  let κ := normalizedMarkOrZero S.intensity
  let hκ := (B.excessState_markBounds B.terminal).mono (fun _ hx => hx.1)
  let Q := finitePoissonDesign S.individuals κ hκ p k
  let C := (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2)
  have hQ := finitePoissonDesign_integrable_maximum S.individuals κ hκ p k
    (S.individuals.integrable_maximum_of_bounded S.individual_bounded) (B.excessState_markIntegrable B.terminal)
  apply csSup_le (B.scalarPayoffs_nonempty w c)
  rintro y ⟨π,rfl⟩
  let πA := π.ignoreIndividualExtras k
  have h0 := π.terminalScalarObjective_le_mappedExcess (c := c) B hw.le
  have h1 := π.mappedExcess_ignoreIndividualExtras B k B.terminal w c
  have h2 := πA.mappedExcessScalarObjective_le_finitePotential Q hQ (B.appendZeroIndividuals k) hμ B.terminal.property hw hc
  have h3 := πA.expectedExcessDesignResidual_bounds B hμ B.terminal p hrate hw hc
  have hl : -C ≤ πA.expectedExcessDesignResidual Q (B.appendZeroIndividuals k) hμ B.terminal w c := h3.1
  change πA.mappedExcessScalarObjective (B.appendZeroIndividuals k) B.terminal w c =
    π.mappedExcessScalarObjective B B.terminal w c at h1
  change πA.mappedExcessScalarObjective (B.appendZeroIndividuals k) B.terminal w c ≤
    Model.optimalScalarValue Q w c - πA.expectedExcessDesignResidual Q (B.appendZeroIndividuals k) hμ B.terminal w c at h2
  change π.scalarObjective B w c ≤ w * (B.terminal : ℝ) + Model.optimalScalarValue Q w c + C
  linarith only [h0,h1,h2,hl]

/-- The lower comparison uses an actual shared rule and independent virtual
clocks, with the source's terminal reward restored on no selection. -/
theorem FiniteIntensityHybridInstance.reserveBernoulliDesign_le_value (B : FiniteIntensityHybridInstance n)
    (hμ : B.intensity ≠ 0) (p : unitInterval)
    (hrate : ((B.excessState B.terminal).intensity : Measure ℝ).real univ = (k : ℝ) * (p : ℝ))
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let S := B.excessState B.terminal
    let κ := normalizedMarkOrZero S.intensity
    let hκ := (B.excessState_markBounds B.terminal).mono (fun _ hx => hx.1)
    let Q := finitePoissonDesign S.individuals κ hκ p k
    w * (B.terminal : ℝ) + Model.optimalScalarValue Q w c ≤ B.optimalScalarValue w c +
      (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) +
        (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) := by
  let S := B.excessState B.terminal
  let κ := normalizedMarkOrZero S.intensity
  let hκ := (B.excessState_markBounds B.terminal).mono (fun _ hx => hx.1)
  let Q := finitePoissonDesign S.individuals κ hκ p k
  have hQ := finitePoissonDesign_integrable_maximum S.individuals κ hκ p k
    (S.individuals.integrable_maximum_of_bounded S.individual_bounded) (B.excessState_markIntegrable B.terminal)
  let π := mappedPositivePotentialPolicy Q hQ B.terminal hw.le hc
  let πS := π.simulateZeroIndividuals
  have h0 := mappedPositivePotentialPolicy_residual_identity Q hQ (B.appendZeroIndividuals k) hμ B.terminal.property hw hc
  have h1 := π.expectedExcessDesignResidual_bounds B hμ B.terminal p hrate hw hc
  have hu : π.expectedExcessDesignResidual Q (B.appendZeroIndividuals k) hμ B.terminal w c ≤
      (k : ℝ) * (w * (p : ℝ) ^ 2 * ∫ x, x ∂κ) +
        (Real.pi / 2) * w * (∫ x, x ∂κ) * Real.sqrt ((k : ℝ) * (p : ℝ) ^ 2) := h1.2
  have h2 := π.mappedExcess_le_simulateZeroIndividuals B B.terminal.property hw.le hc
  have hpos : πS.rule.AcceptsPositiveExcess B.terminal :=
    HybridZeroSimulation.simulate_acceptsPositiveExcess π.rule B.terminal (mappedPositivePotentialRule_acceptsPositiveExcess Q B.terminal w c)
  have h3 := πS.scalarObjective_eq_terminal_add_mappedExcess B hpos w c
  have h4 := B.scalarObjective_le_value πS w c
  change Model.optimalScalarValue Q w c - π.mappedExcessScalarObjective (B.appendZeroIndividuals k) B.terminal w c =
    π.expectedExcessDesignResidual Q (B.appendZeroIndividuals k) hμ B.terminal w c at h0
  change π.mappedExcessScalarObjective (B.appendZeroIndividuals k) B.terminal w c ≤
    πS.mappedExcessScalarObjective B B.terminal w c at h2
  change w * (B.terminal : ℝ) + Model.optimalScalarValue Q w c ≤ _
  linarith only [h0,hu,h2,h3,h4]

end ProphetSecretary.Limiting
