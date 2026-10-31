import ProphetSecretary.Limiting.FixedCountBandTilt
import ProphetSecretary.Limiting.CountableBandCutoff
import ProphetSecretary.Limiting.DirectVirtualScore
import ProphetSecretary.Limiting.FixedRareDesign
import ProphetSecretary.Probability.QuarterLikelihoodBounds

/-!
# Whole prescribed-count designs under the actual zero-atom likelihood tilt

Retained marginal laws are unchanged. Every virtual marginal is identified
with the scaled-intensity rare law at the SAME fixed count. The proof is an
equality of the full finite product instance, including zero-valued identity
observations, before applying any benchmark or value limit.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal Topology
namespace ProphetSecretary.Limiting
open ProphetSecretary.Probability
variable {n : ℕ}

lemma bandScaledIntensity_mass_le_fixedCount (μ : FiniteMeasure ℝ) {S : Set ℝ} (hS : MeasurableSet S)
    (N : ℕ) (hN : 0<N) (hSmall : (μ.mass:ℝ)/(N:ℝ)≤1/2)
    {θ : ℝ} (hθ : |θ|≤1/4) (r : ℝ≥0) (hr : (r:ℝ)=1+θ) :
    (bandScaledIntensity μ S r).mass≤(N:ℝ≥0) := by
  have hBase := (div_le_iff₀ (Nat.cast_pos.mpr hN)).mp hSmall
  have hScaled := bandScaledIntensity_mass_le_quarter μ hS hθ r hr
  have hCount : 0≤(N:ℝ) := Nat.cast_nonneg N
  have hReal : ((bandScaledIntensity μ S r).mass:ℝ)≤(N:ℝ) := by nlinarith only [hBase,hScaled,hCount]
  exact_mod_cast hReal

lemma rareParameter_coe_eq_mass_div (μ : FiniteMeasure ℝ) (N : ℕ) (hN : 0<N)
    (hm : μ.mass≤(N:ℝ≥0)) :
    (rareParameter μ (N:ℝ≥0) (by exact_mod_cast hN) hm:ℝ)=(μ.mass:ℝ)/(N:ℝ) := by
  change (((N:ℝ≥0)⁻¹*μ.mass:ℝ≥0):ℝ)=_
  rw [NNReal.coe_mul,NNReal.coe_inv,NNReal.coe_natCast]
  ring

theorem rareDesign_bandScore_likelihoodWidePath_eq (P : Model.Instance n)
    (μ : FiniteMeasure ℝ) (H : ℝ≥0) (hSupport : ∀ᵐ x ∂(μ:Measure ℝ), x∈Ioc (0:ℝ) H)
    {S : Set ℝ} (hS : MeasurableSet S) (hS0 : (0:ℝ)∉S)
    (N : ℕ) (hN : 0<N) (hm : μ.mass≤(N:ℝ≥0)) (hSmall : (μ.mass:ℝ)/(N:ℝ)≤1/2)
    {θ : ℝ} (hθ : |θ|≤1/4) (r : ℝ≥0) (hr : (r:ℝ)=1+θ)
    (hν : ∀ᵐ x ∂(bandScaledIntensity μ S r:Measure ℝ), x∈Icc (0:ℝ) H) :
    let A := rareDesign P μ H (hSupport.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) N hN hm
    let κ := (rareProbabilityLaw μ (N:ℝ≥0) (by exact_mod_cast hN) hm:Measure ℝ)
    ∀ (hh : ∀ i, Measurable (directCloudScore n N κ S i))
      (hb : ∀ i, ∀ᵐ x ∂A.law i, |directCloudScore n N κ S i x|≤1)
      (hz : ∀ i, (∫ x, directCloudScore n N κ S i x ∂A.law i)=0),
      A.likelihoodWidePath (directCloudScore n N κ S) hh hb hz θ=
        rareDesign P (bandScaledIntensity μ S r) H hν N hN
          (bandScaledIntensity_mass_le_fixedCount μ hS N hN hSmall hθ r hr) := by
  let A := rareDesign P μ H (hSupport.mono (fun _ hx => ⟨hx.1.le,hx.2⟩)) N hN hm
  let κ := (rareProbabilityLaw μ (N:ℝ≥0) (by exact_mod_cast hN) hm:Measure ℝ)
  let ν := bandScaledIntensity μ S r
  let hνMass := bandScaledIntensity_mass_le_fixedCount μ hS N hN hSmall hθ r hr
  let p := rareParameter μ (N:ℝ≥0) (by exact_mod_cast hN) hm
  let pθ := rareParameter ν (N:ℝ≥0) (by exact_mod_cast hN) hνMass
  have hp : (p:ℝ)=(μ.mass:ℝ)/(N:ℝ) := rareParameter_coe_eq_mass_div μ N hN hm
  have hpθ : (pθ:ℝ)=(ν.mass:ℝ)/(N:ℝ) := rareParameter_coe_eq_mass_div ν N hN hνMass
  have hκ : κ=zeroInflatedLaw (normalizedMarkOrZero μ) p := rareProbabilityLaw_eq_zeroInflated μ _ _ _
  have hκθ : (rareProbabilityLaw ν (N:ℝ≥0) (by exact_mod_cast hN) hνMass:Measure ℝ)=
      zeroInflatedLaw (normalizedMarkOrZero ν) pθ := rareProbabilityLaw_eq_zeroInflated ν _ _ _
  have hVirtual : tiltLaw κ (bandScore κ S) θ=(rareProbabilityLaw ν (N:ℝ≥0) (by exact_mod_cast hN) hνMass:Measure ℝ) := by
    rw [hκ,hκθ]
    exact directPoissonMarginal_bandScore_tilt_eq μ H hSupport hS hS0 N p pθ hp
      (hp.trans_le hSmall) hθ r hr hpθ
  dsimp only
  intro hh hb hz
  change A.likelihoodWidePath (directCloudScore n N κ S) hh hb hz θ=_
  rw [A.law_curvature_model_transfer (directCloudScore n N κ S) hh hb hz hθ]
  apply Model.Instance.eq_of_law_eq
  funext i
  induction i using Fin.addCases with
  | left i =>
    change tiltLaw (A.law (i.castAdd N)) (directCloudScore n N κ S (i.castAdd N)) θ=_
    simp only [A,rareDesign,appendIID,directCloudScore,Fin.addCases_left]
    simp only [tiltLaw,tiltFactor,mul_zero,add_zero,ENNReal.ofReal_one]
    change (P.law i).withDensity (1:ℝ → ℝ≥0∞)=P.law i
    exact withDensity_one
  | right j =>
    change tiltLaw (A.law (j.natAdd n)) (directCloudScore n N κ S (j.natAdd n)) θ=_
    simpa only [A,rareDesign,appendIID,directCloudScore,Fin.addCases_right] using hVirtual
end ProphetSecretary.Limiting
