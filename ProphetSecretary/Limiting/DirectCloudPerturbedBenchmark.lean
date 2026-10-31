import ProphetSecretary.Limiting.DirectApproximationBenchmark
import ProphetSecretary.Limiting.FixedCountDesignTilt
import ProphetSecretary.Limiting.CountableBandPolicies

/-!
# Actual perturbed prophet limits at the same base virtual counts

The marginal zero-atom likelihood identity first identifies the entire finite
product law with the scaled-intensity prescribed-count design. The count and
cutoff schedules remain fixed at their base choices. The genuine benchmark
limit then applies to each fixed perturbation, without a first-moment bound.
-/
open MeasureTheory Set Filter
open scoped Classical Topology NNReal
namespace ProphetSecretary.Limiting
open CountableInstance ProphetSecretary.Probability

 theorem CountableInstance.finiteDirectApproximationAt_bandTilt_eq (B : CountableInstance)
    (n : ℕ) (cut : ℝ) (hcut : (B.terminal:ℝ)<cut) (k : ℕ) (hk : 0<k)
    (hm : (B.intensityAbove cut hcut).mass≤(k:ℝ≥0))
    (hSmall : ((B.intensityAbove cut hcut).mass:ℝ)/(k:ℝ)≤1/2)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S)
    {θ : ℝ} (hθ : |θ|≤1/4) (r : ℝ≥0) (hr : (r:ℝ)=1+θ)
    (hmθ : ((B.scaleBand S r).intensityAbove cut hcut).mass≤(k:ℝ≥0)) :
    let A := B.finiteDirectApproximationAt n cut hcut k hk hm
    let κ := (rareProbabilityLaw (B.intensityAbove cut hcut) (k:ℝ≥0) (by exact_mod_cast hk) hm:Measure ℝ)
    ∀ (hh : ∀ i, Measurable (directCloudScore n k κ S i))
      (hb : ∀ i, ∀ᵐ x ∂A.law i, |directCloudScore n k κ S i x|≤1)
      (hz : ∀ i, (∫ x, directCloudScore n k κ S i x ∂A.law i)=0),
      A.likelihoodWidePath (directCloudScore n k κ S) hh hb hz θ=
        (B.scaleBand S r).finiteDirectApproximationAt n cut hcut k hk hmθ := by
  let A := B.finiteDirectApproximationAt n cut hcut k hk hm
  let μ := B.intensityAbove cut hcut
  let κ := (rareProbabilityLaw μ (k:ℝ≥0) (by exact_mod_cast hk) hm:Measure ℝ)
  let ν := bandScaledIntensity μ S r
  have hSupport : ∀ᵐ x ∂(μ:Measure ℝ), x∈Ioc (0:ℝ) B.cap := (B.truncation n cut hcut).intensity_supported
  have hν : ∀ᵐ x ∂(ν:Measure ℝ), x∈Icc (0:ℝ) B.cap := by
    change ∀ᵐ x ∂(bandScaledIntensity μ S r:Measure ℝ), x∈Icc (0:ℝ) B.cap
    rw [bandScaledIntensity_toMeasure μ hS r]
    exact (withDensity_absolutelyContinuous _ _).ae_le (hSupport.mono (fun _ hx => ⟨hx.1.le,hx.2⟩))
  have hInt : (B.scaleBand S r).intensityAbove cut hcut=ν := B.scaleBand_intensityAbove hS r cut hcut
  dsimp only
  intro hh hb hz
  have hRaw := rareDesign_bandScore_likelihoodWidePath_eq (B.individualPrefix n) μ B.cap hSupport hS hS0 k hk hm
    hSmall hθ r hr hν hh hb hz
  have hTarget : rareDesign (B.individualPrefix n) ν B.cap hν k hk
      (bandScaledIntensity_mass_le_fixedCount μ hS k hk hSmall hθ r hr)=
      (B.scaleBand S r).finiteDirectApproximationAt n cut hcut k hk hmθ := by
    apply Model.Instance.eq_of_law_eq
    funext i
    induction i using Fin.addCases with
    | left i =>
      simp only [finiteDirectApproximationAt,CountableInstance.truncation,rareDesign,appendIID,Fin.addCases_left]
      rfl
    | right j =>
      simp only [finiteDirectApproximationAt,CountableInstance.truncation,rareDesign,appendIID,Fin.addCases_right]
      change (rareFiniteLaw ν (k:ℝ≥0):Measure ℝ)=
        (rareFiniteLaw ((B.scaleBand S r).intensityAbove cut hcut) (k:ℝ≥0):Measure ℝ)
      exact congrArg (fun μ : FiniteMeasure ℝ => (rareFiniteLaw μ (k:ℝ≥0):Measure ℝ)) hInt.symm
  exact hRaw.trans hTarget

theorem CountableInstance.direct_cloud_perturbed_expectedMaximum_tendsto (B : CountableInstance) (hZero : B.terminal=0)
    (Ns ks : ℕ → ℕ) (bs : ℕ → ℝ) (hbs : ∀ m, (B.terminal:ℝ)<bs m)
    (hk : ∀ m, 0<ks m) (hm : ∀ m, (B.intensityAbove (bs m) (hbs m)).mass≤(ks m:ℝ≥0))
    (hSmall : ∀ m, ((B.intensityAbove (bs m) (hbs m)).mass:ℝ)/(ks m:ℝ)≤1/2)
    (hNs : Tendsto Ns atTop atTop) (hCut : Tendsto bs atTop (𝓝 (B.terminal:ℝ))) (hKs : Tendsto ks atTop atTop)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S) :
    let A := fun m => B.finiteDirectApproximationAt (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
    let κ := fun m => (rareProbabilityLaw (B.intensityAbove (bs m) (hbs m)) (ks m:ℝ≥0) (by exact_mod_cast hk m) (hm m):Measure ℝ)
    let score := fun m => directCloudScore (Ns m) (ks m) (κ m) S
    ∀ (hh : ∀ m i, Measurable (score m i))
      (hb : ∀ m i, ∀ᵐ x ∂(A m).law i, |score m i x|≤1)
      (hz : ∀ m i, (∫ x, score m i x ∂(A m).law i)=0) θ, |θ|≤1/4 →
      Tendsto (fun m => ((A m).likelihoodWidePath (score m) (hh m) (hb m) (hz m) θ).expectedMaximum) atTop
        (𝓝 (B.bandLikelihoodPath S θ).expectedMaximum) := by
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
  have hLim := D.finiteDirectApproximationAt_expectedMaximum_tendsto hZero Ns ks bs hbs hk hmθ hNs hCut hKs
  have hEq (m) := B.finiteDirectApproximationAt_bandTilt_eq (Ns m) (bs m) (hbs m) (ks m) (hk m) (hm m)
    (hSmall m) hS hS0 hθ r rfl (hmθ m) (hh m) (hb m) (hz m)
  have hPath : B.bandLikelihoodPath S θ=D := B.bandLikelihoodPath_of_mem S hθ
  rw [hPath]
  exact hLim.congr (fun m => (congrArg Model.Instance.expectedMaximum (hEq m)).symm)
end ProphetSecretary.Limiting
