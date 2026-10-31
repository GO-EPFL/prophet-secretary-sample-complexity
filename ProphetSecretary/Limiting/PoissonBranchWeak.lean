import ProphetSecretary.Limiting.FiniteIntensityPoisson
import ProphetSecretary.Probability.WeakAlmostContinuousIntegral
import Mathlib.MeasureTheory.Measure.FiniteMeasurePi
import Mathlib.MeasureTheory.Measure.FiniteMeasureProd

/-!
# Weak convergence on fixed analytical point-count branches

At a nonzero limiting intensity, normalization, the independent uniform
clock product, and every finite iid point array converge weakly. Bounded
almost everywhere continuous branch observables therefore have convergent
expectations; no continuity of an optimizer is presumed.
-/
open MeasureTheory Set Filter TopologicalSpace
open scoped Topology Classical
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability

noncomputable def pointProbabilityLaw (μ : FiniteMeasure ℝ) : ProbabilityMeasure Point :=
  ⟨pointLaw μ,inferInstance⟩
noncomputable def arrayProbabilityLaw (μ : FiniteMeasure ℝ) (N : ℕ) : ProbabilityMeasure (Fin N → Point) :=
  ⟨arrayLaw μ N,inferInstance⟩

lemma pointProbabilityLaw_tendsto {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hZero : μ≠0) :
    Tendsto (fun m => pointProbabilityLaw (μs m)) atTop (𝓝 (pointProbabilityLaw μ)) := by
  let ρ : ProbabilityMeasure ℝ := ⟨Model.Instance.uniformClock,inferInstance⟩
  have hNorm := FiniteMeasure.tendsto_normalize_of_tendsto hμ hZero
  exact ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    ((tendsto_const_nhds : Tendsto (fun _ : ℕ => ρ) atTop (𝓝 ρ)).prodMk_nhds hNorm)

lemma arrayProbabilityLaw_tendsto {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hZero : μ≠0) (N : ℕ) :
    Tendsto (fun m => arrayProbabilityLaw (μs m) N) atTop (𝓝 (arrayProbabilityLaw μ N)) := by
  have hPoint := pointProbabilityLaw_tendsto hμ hZero
  exact ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp
    (tendsto_pi_nhds.mpr (fun _ : Fin N => hPoint))

variable {Aux : Type*} [MeasurableSpace Aux] [TopologicalSpace Aux]
  [SecondCountableTopology Aux] [PseudoMetrizableSpace Aux] [OpensMeasurableSpace Aux]

lemma poissonBranchProbability_tendsto {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hZero : μ≠0)
    {νs : ℕ → ProbabilityMeasure Aux} {ν : ProbabilityMeasure Aux}
    (hν : Tendsto νs atTop (𝓝 ν)) (N : ℕ) :
    Tendsto (fun m => (arrayProbabilityLaw (μs m) N).prod (νs m)) atTop
      (𝓝 ((arrayProbabilityLaw μ N).prod ν)) :=
  ProbabilityMeasure.continuous_prod.continuousAt.tendsto.comp
    ((arrayProbabilityLaw_tendsto hμ hZero N).prodMk_nhds hν)

lemma poissonBranch_integral_tendsto {μs : ℕ → FiniteMeasure ℝ} {μ : FiniteMeasure ℝ}
    (hμ : Tendsto μs atTop (𝓝 μ)) (hZero : μ≠0)
    {νs : ℕ → ProbabilityMeasure Aux} {ν : ProbabilityMeasure Aux}
    (hν : Tendsto νs atTop (𝓝 ν)) (N : ℕ)
    (f : (Fin N → Point) × Aux → ℝ) (hf : Measurable f) {D : ℝ}
    (hb : ∀ q, |f q|≤D)
    (hc : ∀ᵐ q ∂(arrayLaw μ N).prod (ν:Measure Aux), ContinuousAt f q) :
    Tendsto (fun m => ∫ q, f q ∂(arrayLaw (μs m) N).prod (νs m:Measure Aux)) atTop
      (𝓝 (∫ q, f q ∂(arrayLaw μ N).prod (ν:Measure Aux))) :=
  integral_tendsto_of_weak_ae_continuous_bounded (poissonBranchProbability_tendsto hμ hZero hν N) hf hb hc
end ProphetSecretary.Limiting
