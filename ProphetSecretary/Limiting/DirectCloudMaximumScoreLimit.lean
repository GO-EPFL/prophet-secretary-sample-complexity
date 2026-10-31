import ProphetSecretary.Limiting.DirectCloudPerturbedBenchmark
import ProphetSecretary.Limiting.CountableBandMaximumDerivative
import ProphetSecretary.Stability.MaximumScoreLimit

/-!
# Actual direct zero-atom maximum-score expectations

The full fixed-count likelihood family has converging perturbed prophet
benchmarks. Its uniform information-dependent quadratic remainder gives
convergence of their actual derivatives, identified with complete maximum
score expectations. The limiting derivative is the proved Poisson band
likelihood response. No total first-moment bound is imposed.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

theorem CountableInstance.direct_cloud_expectedMaximumScore_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (Ns ks : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal:ℝ)<bs m)
    (hk : ∀ m, 0<ks m) (hm : ∀ m, (B.intensityAbove (bs m) (hbs m)).mass≤(ks m:ℝ≥0))
    (hSmall : ∀ m, ((B.intensityAbove (bs m) (hbs m)).mass:ℝ)/(ks m:ℝ)≤1/2)
    (hNs : Tendsto Ns atTop atTop) (hCut : Tendsto bs atTop (𝓝 (B.terminal:ℝ))) (hKs : Tendsto ks atTop atTop)
    {S : Set ℝ} (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal:ℝ)<b) (hSub : S⊆Ioi b)
    {I : ℝ} (hI : 0≤I) :
    let A := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
    let κ := fun m => (rareProbabilityLaw (B.intensityAbove (bs m) (hbs m)) (ks m:ℝ≥0) (by exact_mod_cast hk m) (hm m):Measure ℝ)
    let score := fun m => directCloudScore (Ns m) (ks m) (κ m) S
    ∀ (hh : ∀ m i, Measurable (score m i))
      (hBound : ∀ m i, ∀ᵐ x ∂(A m).law i, |score m i x|≤1)
      (hz : ∀ m i, (∫ x, score m i x ∂(A m).law i)=0),
      (∀ m, information (A m).law (score m)≤I) →
      Tendsto (fun m => (A m).expectedMaximumScore (score m)) atTop (𝓝 (B.prophetBandLikelihoodDerivative S)) := by
  let A := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
  let κ := fun m => (rareProbabilityLaw (B.intensityAbove (bs m) (hbs m)) (ks m:ℝ≥0) (by exact_mod_cast hk m) (hm m):Measure ℝ)
  let score := fun m => directCloudScore (Ns m) (ks m) (κ m) S
  dsimp only
  intro hh hBound hz hInfo
  have hS0 : (0:ℝ)∉S := fun h => not_lt_of_ge (B.terminal.property.trans hb.le) (hSub h)
  exact Model.expectedMaximumScore_tendsto_of_perturbed_benchmarks (fun m => Ns m+ks m) A B.cap.property hI
    (fun m => B.finiteDirectApproximationAt_bounded (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m))
    score hh hBound hz hInfo (fun θ => (B.bandLikelihoodPath S θ).expectedMaximum)
    (B.hasDerivAt_expectedMaximum_bandLikelihoodPath hS hb hSub)
    (fun θ hθ => B.direct_cloud_perturbed_expectedMaximum_tendsto hZero Ns ks bs hbs hk hm hSmall
      hNs hCut hKs hS hS0 hh hBound hz θ (abs_le.mpr hθ))
end ProphetSecretary.Limiting
