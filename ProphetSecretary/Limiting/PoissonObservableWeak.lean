import ProphetSecretary.Limiting.PoissonBranchWeak
import ProphetSecretary.Limiting.HybridMixture
import ProphetSecretary.Limiting.WeakRareDesign
import ProphetSecretary.Analysis.PoissonWeightedMixtureLimit

/-!
# Weak convergence of count-weighted Poisson observables

The actual Poisson mixture is integrated before passing to the limit. A
linear count bound controls all branches by one summable first-moment
envelope. Branch regularity is an explicit analytic premise, separate from
any stopping-policy assertion.
-/
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology Classical NNReal ENNReal
namespace ProphetSecretary.Limiting

variable {Aux : Type*} [MeasurableSpace Aux]

lemma poissonObservable_integrable_of_linear_count (μ : FiniteMeasure ℝ) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (f : Configuration × Aux → ℝ) (hf : Measurable f) {D : ℝ}
    (hb : ∀ q, |f q|≤D*((q.1.1:ℝ)+1)) : Integrable f (worldLaw μ ν) := by
  have hCount : Integrable (fun q : Configuration × Aux => (q.1.1:ℝ)) (worldLaw μ ν) :=
    (measurePreserving_fst (μ := configurationLaw μ) (ν := ν)).integrable_comp_of_integrable
      (configuration_count_integrable μ)
  exact ((hCount.add (integrable_const 1)).const_mul D).mono'
    hf.aestronglyMeasurable (Eventually.of_forall (fun q => by
      change |f q|≤D*((q.1.1:ℝ)+1)
      exact hb q))

lemma poissonBranch_integral_abs_le (μ : FiniteMeasure ℝ) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (f : Configuration × Aux → ℝ) (_hf : Measurable f) {D : ℝ}
    (hb : ∀ q, |f q|≤D*((q.1.1:ℝ)+1)) (N : ℕ) :
    |∫ q, f (configurationMk N q.1,q.2) ∂(arrayLaw μ N).prod ν| ≤ D*((N:ℝ)+1) := by
  have h := norm_integral_le_of_norm_le_const (μ := (arrayLaw μ N).prod ν)
    (f := fun q => f (configurationMk N q.1,q.2))
    (Eventually.of_forall (fun q => by
      change |f (configurationMk N q.1,q.2)|≤D*((N:ℝ)+1)
      exact hb (configurationMk N q.1,q.2)))
  simpa only [Real.norm_eq_abs,probReal_univ,mul_one] using h

variable [TopologicalSpace Aux] [SecondCountableTopology Aux]
  [PseudoMetrizableSpace Aux] [OpensMeasurableSpace Aux]

/-- Weak convergence for a fixed full-configuration observable whose growth
is at most linear in the analytical count. The limiting intensity is nonzero. -/
theorem poissonObservable_integral_tendsto_of_nonzero
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hZero : μ≠0)
    {νs : ℕ → ProbabilityMeasure Aux} {ν : ProbabilityMeasure Aux}
    (hν : Tendsto νs atTop (𝓝 ν))
    (f : Configuration × Aux → ℝ) (hf : Measurable f) {D : ℝ} (hD : 0≤D)
    (hb : ∀ q, |f q|≤D*((q.1.1:ℝ)+1))
    (hc : ∀ N, ∀ᵐ q ∂(arrayLaw μ N).prod (ν:Measure Aux),
      ContinuousAt (fun q : (Fin N → Point) × Aux => f (configurationMk N q.1,q.2)) q) :
    Tendsto (fun m => ∫ q, f q ∂worldLaw (μs m) (νs m:Measure Aux)) atTop
      (𝓝 (∫ q, f q ∂worldLaw μ (ν:Measure Aux))) := by
  obtain ⟨R,_hR,hRs⟩ := exists_uniform_mass_bound_of_tendsto μs μ hμ
  let b := fun m N => ∫ q, f (configurationMk N q.1,q.2) ∂(arrayLaw (μs m) N).prod (νs m:Measure Aux)
  let v := fun N => ∫ q, f (configurationMk N q.1,q.2) ∂(arrayLaw μ N).prod (ν:Measure Aux)
  have hBranches (N : ℕ) : Tendsto (fun m => b m N) atTop (𝓝 (v N)) := by
    exact poissonBranch_integral_tendsto hμ hZero hν N
      (fun q => f (configurationMk N q.1,q.2))
      (hf.comp (((measurable_configuration_mk N).comp measurable_fst).prodMk measurable_snd))
      (D := D*((N:ℝ)+1)) (fun q => hb (configurationMk N q.1,q.2)) (hc N)
  have hLimit := ProphetSecretary.Analysis.poisson_weighted_tsum_tendsto_of_linear_bound hμ.mass hRs b v hD
    (fun m N => poissonBranch_integral_abs_le (μs m) (νs m:Measure Aux) f hf hb N) hBranches
  have he (κ : FiniteMeasure ℝ) (ρ : ProbabilityMeasure Aux) :
      (∫ q, f q ∂worldLaw κ (ρ:Measure Aux)) =
      ∑' N, poissonWeight κ.mass N*∫ q, f (configurationMk N q.1,q.2) ∂(arrayLaw κ N).prod (ρ:Measure Aux) :=
    integral_worldLaw_fibers κ (ρ:Measure Aux) f hf (poissonObservable_integrable_of_linear_count κ _ f hf hb)
  simpa only [← he,b,v] using hLimit
end ProphetSecretary.Limiting
