import ProphetSecretary.Limiting.WeakHybridFullMarkValue
import ProphetSecretary.Limiting.WeakExcessLaws
import ProphetSecretary.Limiting.HybridReserveShift
import ProphetSecretary.Limiting.WeakHybridBenchmark

/-!
# Weak continuity of bounded finite-hybrid scalar values

The terminal reward is fixed before the original weak-law limit. Its excess
pushforward is kept as a full finite mark law for the finite approximation;
only the actual Poisson state uses the positive restriction. Thus zero excess
atoms need not have continuous mass. The result concerns optimal values over
all admissible hybrid policies and does not infer optimizer convergence.
-/
open MeasureTheory Set Filter
open scoped Topology NNReal Classical BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

/-- Weak scalar continuity at any common terminal reward, uniform for a bounded
reward-weight interval and all nonnegative duration weights. -/
theorem optimalScalarValue_uniform_weak
    (Bs : ℕ → FiniteIntensityHybridInstance n) (B : FiniteIntensityHybridInstance n)
    (H W : ℝ≥0) (hCaps : ∀ m, (Bs m).cap ≤ H) (hCap : B.cap ≤ H)
    (hTerms : ∀ m, (Bs m).terminal = B.terminal)
    (hIndividual : ∀ i, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hIntensity : Tendsto (fun m => (Bs m).intensity) atTop (𝓝 B.intensity)) :
    ∀ ε > (0 : ℝ), ∀ᶠ m in atTop, ∀ w c : ℝ, 0 ≤ w → w ≤ (W : ℝ) → 0 ≤ c →
      |(Bs m).optimalScalarValue w c-B.optimalScalarValue w c| < ε := by
  let Cs := fun m => (Bs m).excessState B.terminal
  let C := B.excessState B.terminal
  let μs := fun m => fullExcessIntensity (Bs m).intensity B.terminal
  let μ := fullExcessIntensity B.intensity B.terminal
  have hsupps (m : ℕ) : ∀ᵐ x ∂(μs m : Measure ℝ), x ∈ Icc (0 : ℝ) H :=
    fullExcessIntensity_bounds (Bs m).intensity B.terminal H
      ((Bs m).intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2.trans (by exact_mod_cast hCaps m)⟩)
  have hsupp : ∀ᵐ x ∂(μ : Measure ℝ), x ∈ Icc (0 : ℝ) H :=
    fullExcessIntensity_bounds B.intensity B.terminal H
      (B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2.trans (by exact_mod_cast hCap)⟩)
  have hweakC : ∀ i, Tendsto (fun m => (Cs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (C.individuals.marginalProbabilityLaw i)) :=
    excessOffers_coordinatewise_weak (fun m => (Bs m).individuals) B.individuals B.terminal hIndividual
  have hweakμ : Tendsto μs atTop (𝓝 μ) := fullExcessIntensity_tendsto hIntensity B.terminal
  have hvalues := optimalScalarValue_uniform_weak_full_mark_laws Cs C μs μ H W hCaps hCap
    (fun _ => rfl) rfl hsupps hsupp
    (fun m => excessIntensity_eq_full_positiveRestriction (Bs m).intensity B.terminal)
    (excessIntensity_eq_full_positiveRestriction B.intensity B.terminal) hweakC hweakμ
  intro ε hε
  filter_upwards [hvalues ε hε] with m hm
  intro w c hw hwW hc
  by_cases hw0 : w = 0
  · subst w
    rw [(Bs m).value_zero_rewardWeight hc,B.value_zero_rewardWeight hc]
    simpa only [sub_self,abs_zero] using hε
  · have hwP : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    rw [(Bs m).value_reserveShift hwP hc,B.value_reserveShift hwP hc,hTerms m]
    simpa only [add_sub_add_left_eq_sub] using hm w c hw hwW hc

/-- Pointwise scalar values converge for arbitrary fixed nonnegative weights;
no optimizer or policy convergence follows from this theorem. -/
theorem optimalScalarValue_tendsto_of_weak
    (Bs : ℕ → FiniteIntensityHybridInstance n) (B : FiniteIntensityHybridInstance n)
    (H : ℝ≥0) (hCaps : ∀ m, (Bs m).cap ≤ H) (hCap : B.cap ≤ H)
    (hTerms : ∀ m, (Bs m).terminal = B.terminal)
    (hIndividual : ∀ i, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (B.individuals.marginalProbabilityLaw i)))
    (hIntensity : Tendsto (fun m => (Bs m).intensity) atTop (𝓝 B.intensity))
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Tendsto (fun m => (Bs m).optimalScalarValue w c) atTop (𝓝 (B.optimalScalarValue w c)) := by
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  filter_upwards [optimalScalarValue_uniform_weak Bs B H ⟨w,hw⟩ hCaps hCap hTerms hIndividual hIntensity ε hε] with m hm
  simpa only [Real.dist_eq] using hm w c hw le_rfl hc

end ProphetSecretary.Limiting
