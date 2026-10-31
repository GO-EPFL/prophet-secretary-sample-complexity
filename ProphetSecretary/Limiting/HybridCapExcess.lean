import ProphetSecretary.Limiting.HybridCapping
import ProphetSecretary.Limiting.BoundedIntensityMoment
import ProphetSecretary.Probability.WeakFiniteStopLoss

/-!
# Actual aggregate excess of a finite-intensity hybrid instance

Individual expectations are summed and the anonymous excess is integrated
against its intensity. Bounded support proves integrability. Moving cap heights
are allowed, including limits at atoms.
-/

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Classical BigOperators
namespace ProphetSecretary.Limiting

lemma integral_finiteIntensity_test_eq_mass_normalized (μ : FiniteMeasure ℝ) (f : ℝ → ℝ) :
    (∫ x, f x ∂(μ : Measure ℝ))=(μ.mass:ℝ)*(∫ x, f x ∂(μ.normalize : Measure ℝ)) := by
  have h : (μ : Measure ℝ)=(μ.mass:ℝ≥0∞) • (μ.normalize : Measure ℝ) :=
    congrArg (fun ν : FiniteMeasure ℝ => (ν : Measure ℝ)) μ.self_eq_mass_smul_normalize
  rw [h,integral_smul_measure]
  rfl

lemma finiteMeasure_tailValue_tendsto (μ : FiniteMeasure ℝ) (H : ℝ≥0)
    (hSupp : ∀ᵐ x ∂(μ : Measure ℝ), x∈Icc (0:ℝ) H)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hK : Tendsto Ks atTop (𝓝 K)) :
    Tendsto (fun m => ∫ x, Model.tailValue (Ks m) x ∂(μ : Measure ℝ)) atTop
      (𝓝 (∫ x, Model.tailValue K x ∂(μ : Measure ℝ))) := by
  have h := ProphetSecretary.Probability.finiteIntensity_stopLoss_tendsto_moving
    (μs:=fun _ : ℕ => μ) tendsto_const_nhds H (fun _ => hSupp) hSupp (NNReal.tendsto_coe.2 hK)
  simpa only [Model.stopLoss,Model.tailValue,max_comm] using h

namespace FiniteIntensityHybridInstance
variable {n : ℕ}

noncomputable def individualCapExcess (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) (i : Fin n) : ℝ :=
  ∫ x, Model.tailValue K x ∂B.individuals.law i

noncomputable def poissonCapExcess (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) : ℝ :=
  ∫ x, Model.tailValue K x ∂(B.intensity : Measure ℝ)

noncomputable def totalCapExcess (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) : ℝ :=
  (∑ i, B.individualCapExcess K i)+B.poissonCapExcess K

lemma individualCapExcess_nonnegative (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) (i : Fin n) :
    0≤B.individualCapExcess K i := integral_nonneg (Model.tailValue_nonnegative K)

lemma poissonCapExcess_nonnegative (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) :
    0≤B.poissonCapExcess K := integral_nonneg (Model.tailValue_nonnegative K)

lemma totalCapExcess_nonnegative (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) :
    0≤B.totalCapExcess K := by
  unfold totalCapExcess
  exact add_nonneg (Finset.sum_nonneg (fun i _ => B.individualCapExcess_nonnegative K i)) (B.poissonCapExcess_nonnegative K)

lemma individualCapExcess_integrable (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) (i : Fin n) :
    Integrable (Model.tailValue K) (B.individuals.law i) :=
  Model.integrable_tailValue _ (B.individuals.integrable_maximum_iff.mp
    (B.individuals.integrable_maximum_of_bounded B.individual_bounded) i) K

lemma poissonCapExcess_integrable (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) :
    Integrable (Model.tailValue K) (B.intensity : Measure ℝ) :=
  Model.integrable_tailValue _ (finiteIntensity_integrable_mark B.intensity B.cap
    (B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩)) K

lemma individualCapExcess_tendsto (B : FiniteIntensityHybridInstance n)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hK : Tendsto Ks atTop (𝓝 K)) (i : Fin n) :
    Tendsto (fun m => B.individualCapExcess (Ks m) i) atTop (𝓝 (B.individualCapExcess K i)) := by
  have hSupp : ∀ᵐ x ∂(B.individuals.marginalProbabilityLaw i : Measure ℝ), x∈Icc (0:ℝ) B.cap :=
    ((B.individuals.nonnegative i).and (B.individual_bounded i))
  exact finiteMeasure_tailValue_tendsto (B.individuals.marginalProbabilityLaw i).toFiniteMeasure B.cap hSupp hK

lemma poissonCapExcess_tendsto (B : FiniteIntensityHybridInstance n)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hK : Tendsto Ks atTop (𝓝 K)) :
    Tendsto (fun m => B.poissonCapExcess (Ks m)) atTop (𝓝 (B.poissonCapExcess K)) :=
  finiteMeasure_tailValue_tendsto B.intensity B.cap (B.intensity_supported.mono fun _ hx => ⟨hx.1.le,hx.2⟩) hK

lemma totalCapExcess_tendsto (B : FiniteIntensityHybridInstance n)
    {Ks : ℕ → ℝ≥0} {K : ℝ≥0} (hK : Tendsto Ks atTop (𝓝 K)) :
    Tendsto (fun m => B.totalCapExcess (Ks m)) atTop (𝓝 (B.totalCapExcess K)) := by
  have hSum := tendsto_finsetSum Finset.univ (fun i _ => B.individualCapExcess_tendsto hK i)
  exact hSum.add (B.poissonCapExcess_tendsto hK)

end FiniteIntensityHybridInstance
end ProphetSecretary.Limiting
