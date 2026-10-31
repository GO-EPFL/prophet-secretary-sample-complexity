import ProphetSecretary.Limiting.BernoulliClockErrorMixture
import ProphetSecretary.Limiting.HybridZeroAppendValue

/-!
# Expected design-loss error for a fixed arbitrary hybrid policy

The original policy is kept fixed before q grows. Its causal lift ignores the
added zero identities. Actual product-law augmentation and projection transport
both loss expectations to one space, and the proved pathwise comparison and
clock-count mixture give an explicit uniform bound. No optimizer convergence
or thinning-policy interface is used.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical
namespace ProphetSecretary.Limiting
variable {n : ℕ}

/-- The error depends on the original retained-plus-anonymous expected count,
not on the added virtual count or the competing policy's seed or history use. -/
theorem RandomizedHybridPolicy.bernoulli_expectedDesignLoss_error
    (π : RandomizedHybridPolicy n) (B : FiniteIntensityHybridInstance n) (ha : B.terminal = 0)
    (hμ : B.intensity ≠ 0) (j : ℕ) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    let q := bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j
    |(π.ignoreIndividualExtras q).expectedDesignActionLoss (B.bernoulliApproximation hμ j)
        (B.appendZeroIndividuals q) w c-π.expectedValueLoss B w c| ≤
      ((n : ℝ)+(B.intensity.mass : ℝ))*B.bernoulliClockErrorBound w j := by
  dsimp only
  let q := bernoulliMultiplicity ((B.intensity : Measure ℝ).real univ) j
  let Q := B.bernoulliApproximation hμ j
  let T := B.appendZeroIndividuals q
  let σ := π.ignoreIndividualExtras q
  let Ω := HybridWorld n (π.Seed × (Fin q → ℝ))
  let Γ : Measure Ω := B.law (π.seedLaw.prod (Model.Instance.clocksLaw q))
  let F : HybridWorld (n+q) π.Seed → ℝ := σ.rule.designActionLoss Q w c
  let G : HybridWorld n π.Seed → ℝ := π.rule.reachedValueLoss B w c
  let H : HybridWorld (n+q) π.Seed → ℝ := B.clockErrorSum Q w c
  have hQ : Integrable Model.Instance.maximum Q.valuesLaw :=
    finitePoissonDesign_integrable_maximum B.individuals _ _ _ _
      (B.individuals.integrable_maximum_of_bounded B.individual_bounded) (B.normalizedMark_integrable hμ)
  have hAug : MeasurePreserving (augmentZeroHybridWorld (n := n) (k := q)) Γ (T.law π.seedLaw) :=
    augmentZeroHybridWorld_measurePreserving B.individuals B.intensity π.seedLaw q
  have hBase : MeasurePreserving (forgetZeroAuxiliaryHybridSeed (n := n) (k := q)) Γ (B.law π.seedLaw) :=
    forgetZeroAuxiliaryHybridSeed_measurePreserving B.individuals B.intensity π.seedLaw q
  have hFM : Measurable F := σ.rule.measurable_designActionLoss σ.measurable_rule Q hQ hw hc
  have hGM : Measurable G := π.rule.measurable_reachedValueLoss π.measurable_rule B hw hc
  have hHM : Measurable H := B.measurable_clockErrorSum Q hQ hw hc
  have hFI : Integrable (fun v : Ω => F (augmentZeroHybridWorld v)) Γ :=
    hAug.integrable_comp_of_integrable (σ.rule.integrable_designActionLoss σ.measurable_rule Q hQ T σ.seedLaw hw hc)
  have hGI : Integrable (fun v : Ω => G (forgetZeroAuxiliaryHybridSeed v)) Γ :=
    hBase.integrable_comp_of_integrable (π.rule.integrable_reachedValueLoss π.measurable_rule B π.seedLaw hw hc)
  have hHI : Integrable (fun v : Ω => H (augmentZeroHybridWorld v)) Γ :=
    hAug.integrable_comp_of_integrable (B.integrable_clockErrorSum Q hQ T π.seedLaw hw hc)
  have hPoint (v : Ω) : |F (augmentZeroHybridWorld v)-G (forgetZeroAuxiliaryHybridSeed v)| ≤ H (augmentZeroHybridWorld v) :=
    π.rule.ignoreIndividualExtras_designLoss_error B Q hQ hw.le hc (forgetZeroAuxiliaryHybridSeed v) v.2.2.2.2
  have hFMean : (∫ v : Ω, F (augmentZeroHybridWorld v) ∂Γ) = σ.expectedDesignActionLoss Q T w c :=
    hAug.hasLaw.integral_comp hFM.aestronglyMeasurable
  have hGMean : (∫ v : Ω, G (forgetZeroAuxiliaryHybridSeed v) ∂Γ) = π.expectedValueLoss B w c :=
    hBase.hasLaw.integral_comp hGM.aestronglyMeasurable
  have hHMean : (∫ v : Ω, H (augmentZeroHybridWorld v) ∂Γ) = ∫ v, H v ∂T.law π.seedLaw :=
    hAug.hasLaw.integral_comp hHM.aestronglyMeasurable
  have hSub : σ.expectedDesignActionLoss Q T w c-π.expectedValueLoss B w c =
      ∫ v : Ω, F (augmentZeroHybridWorld v)-G (forgetZeroAuxiliaryHybridSeed v) ∂Γ := by
    rw [integral_sub hFI hGI,hFMean,hGMean]
  change |σ.expectedDesignActionLoss Q T w c-π.expectedValueLoss B w c| ≤ _
  rw [hSub]
  calc
    _ ≤ ∫ v : Ω, |F (augmentZeroHybridWorld v)-G (forgetZeroAuxiliaryHybridSeed v)| ∂Γ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (fun v : Ω => F (augmentZeroHybridWorld v)-G (forgetZeroAuxiliaryHybridSeed v))
    _ ≤ ∫ v : Ω, H (augmentZeroHybridWorld v) ∂Γ := integral_mono (hFI.sub hGI).abs hHI hPoint
    _ = ∫ v, H v ∂T.law π.seedLaw := hHMean
    _ ≤ _ := B.integral_bernoulliClockErrorSum_le ha hμ j T π.seedLaw hw hc

end ProphetSecretary.Limiting
