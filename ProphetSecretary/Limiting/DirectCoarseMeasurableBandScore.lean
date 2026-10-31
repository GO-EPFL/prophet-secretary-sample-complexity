import ProphetSecretary.Limiting.DirectCoarsePerturbedMean
import ProphetSecretary.Stability.FixedPolicyScoreLimit

/-!
# Fixed coarse score convergence on arbitrary positive measurable bands

The complete-vector likelihood score is analytical and may count ignored or
future offers. Perturbed means converge for the same fixed callback. Uniform
fixed-policy curvature, rather than base value convergence alone, identifies
the limiting score covariance. No relation between the band and the coarse
observation cutoff, and no boundary-null assumption, is needed.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

 theorem CountableInstance.direct_coarse_measurableBand_scalarScore_tendsto
    (B : CountableInstance) (hZero : B.terminal=0)
    (Ns ks : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal:ℝ)<bs m)
    (hk : ∀ m, 0<ks m) (hm : ∀ m, (B.intensityAbove (bs m) (hbs m)).mass≤(ks m:ℝ≥0))
    (hSmall : ∀ m, ((B.intensityAbove (bs m) (hbs m)).mass:ℝ)/(ks m:ℝ)≤1/2)
    (hNs : Tendsto Ns atTop atTop) (hCut : Tendsto bs atTop (𝓝 (B.terminal:ℝ)))
    (hSquare : Tendsto (fun m => ((B.intensityAbove (bs m) (hbs m)).mass:ℝ)^2/(ks m:ℝ)) atTop (𝓝 (0:ℝ)))
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S) (hFinite : B.intensity S<⊤)
    {K : ℕ} (π : RandomizedHybridPolicy K) (d : ℝ) (hd : (B.terminal:ℝ)<d)
    {w c I : ℝ} (hw : 0≤w) (hc : 0≤c) (hI : 0≤I) :
    let A := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
    let κ := fun m => (rareProbabilityLaw (B.intensityAbove (bs m) (hbs m)) (ks m:ℝ≥0) (by exact_mod_cast hk m) (hm m):Measure ℝ)
    let score := fun m => directCloudScore (Ns m) (ks m) (κ m) S
    ∀ (hh : ∀ m i, Measurable (score m i))
      (hb : ∀ m i, ∀ᵐ x ∂(A m).law i, |score m i x|≤1)
      (hz : ∀ m i, (∫ x, score m i x ∂(A m).law i)=0),
      (∀ m, information (A m).law (score m)≤I) →
      Tendsto (fun m => w*(directCoarsePolicy (Ns m) (ks m) π d).expectedRewardScore (A m) (score m)+
        c*(directCoarsePolicy (Ns m) (ks m) π d).expectedDurationScore (A m) (score m)) atTop
        (𝓝 ((π.extendToCountable B hd).scalarBandLikelihoodDerivative S w c)) := by
  dsimp only
  intro hh hb hz hInfo
  exact Model.expectedScalarScore_tendsto_of_perturbed_policy_means
    (fun m => Ns m+ks m) _ (fun m => directCoarsePolicy (Ns m) (ks m) π d) B.cap.property hI hw hc
    (fun m => B.finiteDirectApproximationAt_bounded (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m))
    _ hh hb hz hInfo _
    ((π.extendToCountable B hd).hasDerivAt_scalarObjective_bandLikelihoodPolicy_of_finite hS hFinite hw hc)
    (fun θ hθ => B.direct_coarse_perturbed_mean_tendsto hZero Ns ks bs hbs hk hm hSmall hNs hCut hSquare
      hS hS0 hFinite π d hd w c hh hb hz θ (abs_le.mpr hθ))
end ProphetSecretary.Limiting
