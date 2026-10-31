import ProphetSecretary.Limiting.DirectPrescribedCoarseEvaluation
import ProphetSecretary.Limiting.DirectCloudPerturbedValue
import ProphetSecretary.Limiting.CountableFiniteBandResponses

/-!
# Actual perturbed means of a fixed coarse callback

The retained prefix, cutoff and callback are fixed before perturbing. The
zero-atom likelihood identity identifies the full finite evaluation law with
the prescribed-count scaled-intensity law. Both its count and its truncation
schedule are the unperturbed ones. The affected measurable set may cross the
observation cutoff.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

 theorem CountableInstance.direct_coarse_perturbed_mean_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (Ns ks : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal:ℝ)<bs m)
    (hk : ∀ m, 0<ks m) (hm : ∀ m, (B.intensityAbove (bs m) (hbs m)).mass≤(ks m:ℝ≥0))
    (hSmall : ∀ m, ((B.intensityAbove (bs m) (hbs m)).mass:ℝ)/(ks m:ℝ)≤1/2)
    (hNs : Tendsto Ns atTop atTop) (hCut : Tendsto bs atTop (𝓝 (B.terminal:ℝ)))
    (hSquare : Tendsto (fun m => ((B.intensityAbove (bs m) (hbs m)).mass:ℝ)^2/(ks m:ℝ)) atTop (𝓝 (0:ℝ)))
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S) (hFinite : B.intensity S<⊤)
    {K : ℕ} (π : RandomizedHybridPolicy K) (d : ℝ) (hd : (B.terminal:ℝ)<d) (w c : ℝ) :
    let A := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
    let κ := fun m => (rareProbabilityLaw (B.intensityAbove (bs m) (hbs m)) (ks m:ℝ≥0) (by exact_mod_cast hk m) (hm m):Measure ℝ)
    let score := fun m => directCloudScore (Ns m) (ks m) (κ m) S
    ∀ (hh : ∀ m i, Measurable (score m i))
      (hb : ∀ m i, ∀ᵐ x ∂(A m).law i, |score m i x|≤1)
      (hz : ∀ m i, (∫ x, score m i x ∂(A m).law i)=0) θ, |θ|≤1/4 →
      Tendsto (fun m => (directCoarsePolicy (Ns m) (ks m) π d).scalarObjective
        ((A m).likelihoodWidePath (score m) (hh m) (hb m) (hz m) θ) w c) atTop
        (𝓝 (((π.extendToCountable B hd).finiteBandLikelihoodPolicy hS hFinite θ).scalarObjective w c)) := by
  let A := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
  let κ := fun m => (rareProbabilityLaw (B.intensityAbove (bs m) (hbs m)) (ks m:ℝ≥0) (by exact_mod_cast hk m) (hm m):Measure ℝ)
  let score := fun m => directCloudScore (Ns m) (ks m) (κ m) S
  dsimp only
  intro hh hb hz θ hθ
  let r : ℝ≥0 := ⟨1+θ,by linarith only [(abs_le.mp hθ).1]⟩
  let D := B.scaleBand S r
  have hmθ (m) : (D.intensityAbove (bs m) (hbs m)).mass≤(ks m:ℝ≥0) := by
    rw [B.scaleBand_intensityAbove hS r (bs m) (hbs m)]
    exact bandScaledIntensity_mass_le_fixedCount _ hS (ks m) (hk m) (hSmall m) hθ r rfl
  have hSquareθ : Tendsto (fun m => ((D.intensityAbove (bs m) (hbs m)).mass:ℝ)^2/(ks m:ℝ)) atTop (𝓝 (0:ℝ)) := by
    have h := bandScaledIntensity_square_error_tendsto (fun m => B.intensityAbove (bs m) (hbs m)) ks hS hθ r rfl hSquare
    exact h.congr (fun m => congrArg (fun μ : FiniteMeasure ℝ => (μ.mass:ℝ)^2/(ks m:ℝ))
      (B.scaleBand_intensityAbove hS r (bs m) (hbs m)).symm)
  have hLim := D.directPrescribed_coarse_payoffs_tendsto hZero Ns ks bs hbs hk hmθ hNs hCut hSquareθ π d hd
  have hEq (m) := B.finiteDirectApproximationAt_bandTilt_eq (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
    (hSmall m) hS hS0 hθ r rfl (hmθ m) (hh m) (hb m) (hz m)
  have hPath : B.bandLikelihoodPath S θ=D := B.bandLikelihoodPath_of_mem S hθ
  have hTarget : ((π.extendToCountable B hd).finiteBandLikelihoodPolicy hS hFinite θ).scalarObjective w c=
      (π.extendToCountable D hd).scalarObjective w c := by
    rw [RandomizedCountablePolicy.scalarObjective_eq_integral,RandomizedCountablePolicy.scalarObjective_eq_integral]
    change (∫ v, w*(extendTruncatedRule π.rule d).realizedReward (B.bandLikelihoodPath S θ).terminal v+
      c*(extendTruncatedRule π.rule d).realizedDuration v ∂(B.bandLikelihoodPath S θ).completeWorldLaw π.seedLaw)=_
    rw [hPath]
    rfl
  rw [hTarget]
  have h := (hLim.1.const_mul w).add (hLim.2.const_mul c)
  have hScalar : (π.extendToCountable D hd).scalarObjective w c=
      w*(π.extendToCountable D hd).expectedReward+c*(π.extendToCountable D hd).expectedDuration := rfl
  rw [← hScalar] at h
  apply h.congr
  intro m
  rw [← (directCoarsePolicy (Ns m) (ks m) π d).scalarObjective_eq
    (D.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hmθ m))
    ((D.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hmθ m)).integrable_maximum_of_bounded
      (D.finiteDirectApproximationAt_bounded (Ns m) (bs m) (hbs m) (ks m) (hk m) (hmθ m))) w c,hEq m]
end ProphetSecretary.Limiting
