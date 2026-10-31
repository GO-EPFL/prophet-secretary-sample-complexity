import ProphetSecretary.Limiting.LabeledRemainderBand
import ProphetSecretary.Limiting.PositiveIntensityBand
import ProphetSecretary.Limiting.CausalPoissonBand
import ProphetSecretary.Limiting.PoissonBandBenchmark
import ProphetSecretary.Limiting.CountablePrefixState
import ProphetSecretary.Limiting.WeakHybridValue
import ProphetSecretary.Limiting.WeakHybridBenchmark

/-!
# Finite positive-band approximation without an ordering restriction

The retained prefix uses the chosen labels, including padded zero identities.
Only the remainder is Poissonized. The actual causal comparison has explicit
squared-rarity error, independent of retained dimension and duration weight.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal BigOperators
namespace ProphetSecretary.Limiting
variable {n : ℕ}

noncomputable def labeledBandState (P : Model.Instance n) (N : ℕ) (H b : ℝ≥0)
    (hbH : b≤H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) : FiniteIntensityHybridInstance N :=
  poissonizedBandFamily (labeledPrefix P N) (labeledRemainder P N) H b hbH
    (labeledPrefix_bounded P N H.property hcap) (labeledRemainder_bounded P N H.property hcap)

lemma labeledBandState_intensity (P : Model.Instance n) (N : ℕ) (H b : ℝ≥0)
    (hbH : b≤H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) :
    (labeledBandState P N H b hbH hcap).intensity=labeledBandResidual P N b := by
  change (positiveOfferIntensity (labeledRemainder P N)).restrict (Ioi (b : ℝ))=_
  exact (positiveOfferIntensity_restrict_band (labeledRemainder P N) b.property).trans
    (labeledRemainder_band_sum P N b.property)

lemma labeledPrefix_marginalProbabilityLaw (P : Model.Instance n) (N : ℕ) (i : Fin N) :
    (labeledPrefix P N).marginalProbabilityLaw i=labeledPaddedLaw P i.val := by
  apply ProbabilityMeasure.toMeasure_injective
  rfl

theorem labeledBandState_value_comparison (P : Model.Instance n) (N : ℕ) (H b : ℝ≥0)
    (hbH : b≤H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ))
    {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    |Model.optimalTerminalScalarValue P b w c-(labeledBandState P N H b hbH hcap).optimalScalarValue w c|≤
      (Real.pi/2)*w*(H : ℝ)*Real.sqrt (∑ i : Fin n, ((labeledRemainder P N).law i).real (Ioi (b : ℝ))^2) := by
  let S := (labeledPrefix P N).appendIndependent (labeledRemainder P N)
  have hV : Model.optimalTerminalScalarValue S b w c=Model.optimalTerminalScalarValue P b w c :=
    (congrArg (fun T : Model.Instance (N+n) => Model.optimalTerminalScalarValue T b w c)
      (labeledPrefix_append_remainder P N)).trans
      (labeledPrefix_full_terminal_value P N (P.integrable_maximum_of_bounded hcap) b.property hw hc)
  have h := causalPoisson_band_comparison (labeledPrefix P N) (labeledRemainder P N) H b hbH
    (labeledPrefix_bounded P N H.property hcap) (labeledRemainder_bounded P N H.property hcap) hw hc
  change |Model.optimalTerminalScalarValue S b w c-(labeledBandState P N H b hbH hcap).optimalScalarValue w c|≤_ at h
  rw [hV] at h
  exact h

theorem labeledBandState_benchmark_comparison (P : Model.Instance n) (N : ℕ) (H b : ℝ≥0)
    (hbH : b≤H) (hcap : ∀ i, ∀ᵐ x ∂P.law i, x≤(H : ℝ)) :
    0≤P.expectedTerminalMaximum b-(labeledBandState P N H b hbH hcap).expectedMaximum ∧
      P.expectedTerminalMaximum b-(labeledBandState P N H b hbH hcap).expectedMaximum≤
        (H : ℝ)*(∑ i : Fin n, ((labeledRemainder P N).law i).real (Ioi (b : ℝ))^2) := by
  let S := (labeledPrefix P N).appendIndependent (labeledRemainder P N)
  have hM : S.expectedTerminalMaximum b=P.expectedTerminalMaximum b :=
    (congrArg (fun T : Model.Instance (N+n) => T.expectedTerminalMaximum b)
      (labeledPrefix_append_remainder P N)).trans
      (labeledPrefix_full_terminal_benchmark P N (P.integrable_maximum_of_bounded hcap) b.property)
  have h := finite_poisson_band_benchmark_comparison (labeledPrefix P N) (labeledRemainder P N) H b hbH
    (labeledPrefix_bounded P N H.property hcap) (labeledRemainder_bounded P N H.property hcap)
  change 0≤S.expectedTerminalMaximum b-(labeledBandState P N H b hbH hcap).expectedMaximum ∧
    S.expectedTerminalMaximum b-(labeledBandState P N H b hbH hcap).expectedMaximum≤_ at h
  rw [hM] at h
  exact h

lemma labeledBandState_uniform_weak (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (N : ℕ) (b W : ℝ≥0) (hbH : b≤B.cap)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    (μ : FiniteMeasure ℝ) (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x∈Ioc (0 : ℝ) B.cap)
    (hIndividuals : ∀ i, Tendsto (fun m => labeledPaddedLaw (P m) i) atTop (𝓝 (B.individuals i)))
    (hIntensity : Tendsto (fun m => labeledBandResidual (P m) N b) atTop (𝓝 μ)) :
    ∀ ε>(0 : ℝ), ∀ᶠ m in atTop, ∀ w c : ℝ, 0≤w → w≤W → 0≤c →
      |(labeledBandState (P m) N B.cap b hbH (hcap m)).optimalScalarValue w c-
        (B.prefixIntensityState N b hbH μ hμ).optimalScalarValue w c|<ε := by
  let Bs := fun m => labeledBandState (P m) N B.cap b hbH (hcap m)
  let D := B.prefixIntensityState N b hbH μ hμ
  have hP : ∀ i : Fin N, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (D.individuals.marginalProbabilityLaw i)) := by
    intro i
    have hs : (fun m => (Bs m).individuals.marginalProbabilityLaw i)=fun m => labeledPaddedLaw (P m) i.val := by
      funext m
      exact labeledPrefix_marginalProbabilityLaw (P m) N i
    have he : D.individuals.marginalProbabilityLaw i=B.individuals i.val :=
      B.individualPrefix_marginalProbabilityLaw N i
    rw [hs,he]
    exact hIndividuals i.val
  have hμs : Tendsto (fun m => (Bs m).intensity) atTop (𝓝 D.intensity) := by
    have he : (fun m => (Bs m).intensity)=fun m => labeledBandResidual (P m) N b := by
      funext m
      exact labeledBandState_intensity (P m) N B.cap b hbH (hcap m)
    rw [he]
    exact hIntensity
  exact optimalScalarValue_uniform_weak Bs D B.cap W (fun _ => le_rfl) le_rfl (fun _ => rfl) hP hμs

lemma labeledBandState_expectedMaximum_tendsto (sizes : ℕ → ℕ) (P : ∀ m, Model.Instance (sizes m))
    (B : CountableInstance) (N : ℕ) (b : ℝ≥0) (hbH : b≤B.cap)
    (hcap : ∀ m i, ∀ᵐ x ∂(P m).law i, x≤(B.cap : ℝ))
    (μ : FiniteMeasure ℝ) (hμ : ∀ᵐ x ∂(μ : Measure ℝ), x∈Ioc (0 : ℝ) B.cap)
    (hIndividuals : ∀ i, Tendsto (fun m => labeledPaddedLaw (P m) i) atTop (𝓝 (B.individuals i)))
    (hIntensity : Tendsto (fun m => labeledBandResidual (P m) N b) atTop (𝓝 μ)) :
    Tendsto (fun m => (labeledBandState (P m) N B.cap b hbH (hcap m)).expectedMaximum) atTop
      (𝓝 (B.prefixIntensityState N b hbH μ hμ).expectedMaximum) := by
  let Bs := fun m => labeledBandState (P m) N B.cap b hbH (hcap m)
  let D := B.prefixIntensityState N b hbH μ hμ
  have hP : ∀ i : Fin N, Tendsto (fun m => (Bs m).individuals.marginalProbabilityLaw i) atTop
      (𝓝 (D.individuals.marginalProbabilityLaw i)) := by
    intro i
    have hs : (fun m => (Bs m).individuals.marginalProbabilityLaw i)=fun m => labeledPaddedLaw (P m) i.val := by
      funext m
      exact labeledPrefix_marginalProbabilityLaw (P m) N i
    have he : D.individuals.marginalProbabilityLaw i=B.individuals i.val :=
      B.individualPrefix_marginalProbabilityLaw N i
    rw [hs,he]
    exact hIndividuals i.val
  have hμs : Tendsto (fun m => (Bs m).intensity) atTop (𝓝 D.intensity) := by
    have he : (fun m => (Bs m).intensity)=fun m => labeledBandResidual (P m) N b := by
      funext m
      exact labeledBandState_intensity (P m) N B.cap b hbH (hcap m)
    rw [he]
    exact hIntensity
  exact expectedMaximum_tendsto_of_weak Bs D B.cap (fun _ => le_rfl) le_rfl (fun _ => rfl) hP hμs

end ProphetSecretary.Limiting
