import ProphetSecretary.Limiting.DirectCloudPerturbedBenchmark

/-!
# Scalar value limits for the actual fixed-count cloud likelihood family

The quarter perturbation multiplies the finite intensity mass by at most 5/4.
Its squared-intensity/count approximation error is therefore at most 25/16
of the base error. The same fixed counts and cutoffs give the genuine
perturbed value limit; neither a new schedule nor a first-moment bound is used.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

lemma bandScaledIntensity_square_error_tendsto (μs : ℕ → FiniteMeasure ℝ) (ks : ℕ → ℕ)
    {S : Set ℝ} (hS : MeasurableSet S) {θ : ℝ} (hθ : |θ|≤1/4) (r : ℝ≥0) (hr : (r:ℝ)=1+θ)
    (hBase : Tendsto (fun m => ((μs m).mass:ℝ)^2/(ks m:ℝ)) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun m => ((bandScaledIntensity (μs m) S r).mass:ℝ)^2/(ks m:ℝ)) atTop (𝓝 (0:ℝ)) := by
  have hBound (m) : ((bandScaledIntensity (μs m) S r).mass:ℝ)^2/(ks m:ℝ)≤
      (25/16)*(((μs m).mass:ℝ)^2/(ks m:ℝ)) := by
    have hMass := bandScaledIntensity_mass_le_quarter (μs m) hS hθ r hr
    have hPow := pow_le_pow_left₀ (NNReal.coe_nonneg (bandScaledIntensity (μs m) S r).mass) hMass 2
    calc
      _ ≤ ((5/4)*((μs m).mass:ℝ))^2/(ks m:ℝ) := div_le_div_of_nonneg_right hPow (Nat.cast_nonneg (ks m))
      _ = _ := by ring
  have hUpper : Tendsto (fun m => (25/16)*(((μs m).mass:ℝ)^2/(ks m:ℝ))) atTop (𝓝 (0:ℝ)) := by
    simpa only [mul_zero] using hBase.const_mul (25/16:ℝ)
  exact squeeze_zero (fun _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hBound hUpper

theorem CountableInstance.direct_cloud_perturbed_value_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (Ns ks : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal:ℝ)<bs m)
    (hk : ∀ m, 0<ks m) (hm : ∀ m, (B.intensityAbove (bs m) (hbs m)).mass≤(ks m:ℝ≥0))
    (hSmall : ∀ m, ((B.intensityAbove (bs m) (hbs m)).mass:ℝ)/(ks m:ℝ)≤1/2)
    (hNs : Tendsto Ns atTop atTop) (hCut : Tendsto bs atTop (𝓝 (B.terminal:ℝ)))
    (hSquare : Tendsto (fun m => ((B.intensityAbove (bs m) (hbs m)).mass:ℝ)^2/(ks m:ℝ)) atTop (𝓝 (0:ℝ)))
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S) {w c : ℝ} (hw : 0≤w) (hc : 0≤c) :
    let A := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
    let κ := fun m => (rareProbabilityLaw (B.intensityAbove (bs m) (hbs m)) (ks m:ℝ≥0) (by exact_mod_cast hk m) (hm m):Measure ℝ)
    let score := fun m => directCloudScore (Ns m) (ks m) (κ m) S
    ∀ (hh : ∀ m i, Measurable (score m i))
      (hb : ∀ m i, ∀ᵐ x ∂(A m).law i, |score m i x|≤1)
      (hz : ∀ m i, (∫ x, score m i x ∂(A m).law i)=0) θ, |θ|≤1/4 →
      Tendsto (fun m => Model.optimalScalarValue ((A m).likelihoodWidePath (score m) (hh m) (hb m) (hz m) θ) w c) atTop
        (𝓝 ((B.bandLikelihoodPath S θ).optimalScalarValue w c)) := by
  let A := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
  let κ := fun m => (rareProbabilityLaw (B.intensityAbove (bs m) (hbs m)) (ks m:ℝ≥0) (by exact_mod_cast hk m) (hm m):Measure ℝ)
  let score := fun m => directCloudScore (Ns m) (ks m) (κ m) S
  dsimp only
  intro hh hb hz θ hθ
  let r : ℝ≥0 := ⟨1+θ,by have h := (abs_le.mp hθ).1;linarith⟩
  let D := B.scaleBand S r
  have hmθ (m) : (D.intensityAbove (bs m) (hbs m)).mass≤(ks m:ℝ≥0) := by
    change ((B.scaleBand S r).intensityAbove (bs m) (hbs m)).mass≤_
    rw [B.scaleBand_intensityAbove hS r (bs m) (hbs m)]
    exact bandScaledIntensity_mass_le_fixedCount _ hS (ks m) (hk m) (hSmall m) hθ r rfl
  have hSquareθ : Tendsto (fun m => ((D.intensityAbove (bs m) (hbs m)).mass:ℝ)^2/(ks m:ℝ)) atTop (𝓝 (0:ℝ)) := by
    have h := bandScaledIntensity_square_error_tendsto (fun m => B.intensityAbove (bs m) (hbs m)) ks hS hθ r rfl hSquare
    exact h.congr (fun m => congrArg (fun μ : FiniteMeasure ℝ => (μ.mass:ℝ)^2/(ks m:ℝ))
      (B.scaleBand_intensityAbove hS r (bs m) (hbs m)).symm)
  have hLim := D.finiteDirectApproximationAt_value_tendsto hZero Ns ks bs hbs hk hmθ hNs hCut hSquareθ hw hc
  have hEq (m) := B.finiteDirectApproximationAt_bandTilt_eq (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
    (hSmall m) hS hS0 hθ r rfl (hmθ m) (hh m) (hb m) (hz m)
  have hPath : B.bandLikelihoodPath S θ=D := B.bandLikelihoodPath_of_mem S hθ
  rw [hPath]
  exact hLim.congr (fun m => (congrArg (fun P => Model.optimalScalarValue P w c) (hEq m)).symm)
end ProphetSecretary.Limiting
