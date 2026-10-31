import ProphetSecretary.Limiting.PoissonObservableZero

/-!
# Weak convergence of full finite-intensity Poisson observables

The zero-intensity boundary is handled by an explicit empty-configuration
error. Thus the theorem includes zero intensities without asserting weak
convergence of normalized zero-mass mark distributions.
-/
open MeasureTheory ProbabilityTheory Set Filter TopologicalSpace
open scoped Topology Classical NNReal ENNReal
namespace ProphetSecretary.Limiting
variable {Aux : Type*} [MeasurableSpace Aux]

lemma poissonObservable_integral_zero (ν : Measure Aux) [IsProbabilityMeasure ν]
    (f : Configuration × Aux → ℝ) (hf : Measurable f) :
    (∫ q, f q ∂worldLaw (0 : FiniteMeasure ℝ) ν) = ∫ r, f (emptyConfiguration,r) ∂ν := by
  rw [worldLaw,configurationLaw_zero,Measure.dirac_prod]
  exact integral_map (by fun_prop : Measurable (Prod.mk emptyConfiguration)).aemeasurable hf.aestronglyMeasurable

variable [TopologicalSpace Aux] [SecondCountableTopology Aux]
  [PseudoMetrizableSpace Aux] [OpensMeasurableSpace Aux]

/-- Every branch-continuous measurable observable of at most linear count
growth has convergent expectations under the actual constructed laws. -/
theorem poissonObservable_integral_tendsto_of_relevant_branches
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ))
    {νs : ℕ → ProbabilityMeasure Aux} {ν : ProbabilityMeasure Aux}
    (hν : Tendsto νs atTop (𝓝 ν))
    (f : Configuration × Aux → ℝ) (hf : Measurable f) {D : ℝ} (hD : 0≤D)
    (hb : ∀ q, |f q|≤D*((q.1.1:ℝ)+1))
    (hc : ∀ N, μ≠0 ∨ N=0 → ∀ᵐ q ∂(arrayLaw μ N).prod (ν:Measure Aux),
      ContinuousAt (fun q : (Fin N → Point) × Aux => f (configurationMk N q.1,q.2)) q) :
    Tendsto (fun m => ∫ q, f q ∂worldLaw (μs m) (νs m:Measure Aux)) atTop
      (𝓝 (∫ q, f q ∂worldLaw μ (ν:Measure Aux))) := by
  by_cases hZero : μ=0
  · subst μ
    let v0 : Fin 0 → Point := fun j => Fin.elim0 j
    have hMP : MeasurePreserving (fun r : Aux => (v0,r)) (ν:Measure Aux)
        ((arrayLaw (0 : FiniteMeasure ℝ) 0).prod (ν:Measure Aux)) := by
      rw [arrayLaw,Measure.pi_of_empty _ v0,Measure.dirac_prod]
      exact ⟨by fun_prop,rfl⟩
    have hEmptyMeas : Measurable (fun r : Aux => f (emptyConfiguration,r)) :=
      hf.comp (measurable_const.prodMk measurable_id)
    have hEmptyBound (r : Aux) : |f (emptyConfiguration,r)|≤D := by
      simpa only [emptyConfiguration,configurationMk,Nat.cast_zero,zero_add,mul_one] using hb (emptyConfiguration,r)
    have hEmptyCont : ∀ᵐ r ∂(ν:Measure Aux), ContinuousAt (fun r => f (emptyConfiguration,r)) r := by
      filter_upwards [hMP.quasiMeasurePreserving.ae (hc 0 (Or.inr rfl))] with r hr
      have hC := hr.comp (x := r) (continuous_const.prodMk continuous_id).continuousAt
      exact hC
    have hEmptyLimit := ProphetSecretary.Probability.integral_tendsto_of_weak_ae_continuous_bounded
      hν hEmptyMeas hEmptyBound hEmptyCont
    have hMass : Tendsto (fun m => ((μs m).mass:ℝ)) atTop (𝓝 (0:ℝ)) := by
      simpa only [FiniteMeasure.mass,FiniteMeasure.coeFn_zero,Pi.zero_apply,NNReal.coe_zero] using NNReal.tendsto_coe.2 hμ.mass
    have hBoundLimit : Tendsto (fun m => 3*D*((μs m).mass:ℝ)) atTop (𝓝 (0:ℝ)) := by
      simpa only [mul_zero] using hMass.const_mul (3*D)
    have hAbs := squeeze_zero (fun _ => abs_nonneg _)
      (fun m => poissonObservable_empty_error (μs m) (νs m:Measure Aux) f hf hD hb) hBoundLimit
    have hDifference : Tendsto (fun m => (∫ q, f q ∂worldLaw (μs m) (νs m:Measure Aux))-
        ∫ r, f (emptyConfiguration,r) ∂(νs m:Measure Aux)) atTop (𝓝 (0:ℝ)) := by
      apply tendsto_iff_norm_sub_tendsto_zero.mpr
      simpa only [sub_zero,Real.norm_eq_abs] using hAbs
    have hLimit := hDifference.add hEmptyLimit
    have hEq : (fun m => ((∫ q, f q ∂worldLaw (μs m) (νs m:Measure Aux))-
        ∫ r, f (emptyConfiguration,r) ∂(νs m:Measure Aux))+
        ∫ r, f (emptyConfiguration,r) ∂(νs m:Measure Aux)) =
        (fun m => ∫ q, f q ∂worldLaw (μs m) (νs m:Measure Aux)) := by funext m; ring
    rw [hEq,zero_add,← poissonObservable_integral_zero _ f hf] at hLimit
    exact hLimit
  · exact poissonObservable_integral_tendsto_of_nonzero hμ hZero hν f hf hD hb (fun N => hc N (Or.inl hZero))
/-- The all-branches version is useful when regularity is known uniformly
under every normalized evaluation mark distribution. -/
theorem poissonObservable_integral_tendsto
    {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ))
    {νs : ℕ → ProbabilityMeasure Aux} {ν : ProbabilityMeasure Aux}
    (hν : Tendsto νs atTop (𝓝 ν))
    (f : Configuration × Aux → ℝ) (hf : Measurable f) {D : ℝ} (hD : 0≤D)
    (hb : ∀ q, |f q|≤D*((q.1.1:ℝ)+1))
    (hc : ∀ N, ∀ᵐ q ∂(arrayLaw μ N).prod (ν:Measure Aux),
      ContinuousAt (fun q : (Fin N → Point) × Aux => f (configurationMk N q.1,q.2)) q) :
    Tendsto (fun m => ∫ q, f q ∂worldLaw (μs m) (νs m:Measure Aux)) atTop
      (𝓝 (∫ q, f q ∂worldLaw μ (ν:Measure Aux))) :=
  poissonObservable_integral_tendsto_of_relevant_branches hμ hν f hf hD hb (fun N _ => hc N)
end ProphetSecretary.Limiting
