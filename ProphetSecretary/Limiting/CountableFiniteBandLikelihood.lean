import ProphetSecretary.Limiting.CountableFiniteRegionCounts
import ProphetSecretary.Limiting.CountableBandLikelihood
import ProphetSecretary.Probability.PoissonGeometricMoments

/-!
# Likelihoods for finite-intensity sets meeting infinitely many bands

Finite prefix likelihoods converge to the likelihood of the actual complete
count. An integrable geometric-count envelope controls all prefixes. Finite
cylinders then identify the changed independent product law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal ENNReal Topology
namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def prefixBandLikelihood (B : CountableInstance) (S : Set ℝ) (r : ℝ≥0)
    (N : ℕ) (ω : BandConfigurations) : ℝ :=
  ∏ k∈Finset.range N, bandPoissonLikelihood (B.bandIntensity k) S r (ω k)

lemma fullTime_region_finite (B : CountableInstance) {S : Set ℝ} (hFinite : B.intensity S<⊤) :
    (Model.Instance.uniformClock.prod B.intensity) (univ ×ˢ S)<⊤ := by
  simpa only [Measure.prod_prod,measure_univ,one_mul] using hFinite

lemma prefixRegionRate_fullTime_coe (B : CountableInstance) (S : Set ℝ) (N : ℕ) :
    (B.prefixRegionRate (univ ×ˢ S) N : ℝ)=∑ k∈Finset.range N, (B.bandIntensity k S : ℝ) := by
  simp only [prefixRegionRate,NNReal.coe_sum,countRate_coe_eq_intensity,ProphetSecretary.Limiting.intensity,
    Measure.real,Measure.prod_prod,measure_univ,one_mul]
  rfl

lemma prefixBandLikelihood_eq (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    (r : ℝ≥0) (N : ℕ) (ω : BandConfigurations) :
    B.prefixBandLikelihood S r N ω=
      Real.exp ((1-(r : ℝ))*(B.prefixRegionRate (univ ×ˢ S) N : ℝ))*
        (r : ℝ)^(∑ k∈Finset.range N, pointCount (univ ×ˢ S) (ω k)) := by
  unfold prefixBandLikelihood
  simp_rw [bandPoissonLikelihood_eq _ hS r]
  rw [Finset.prod_mul_distrib,←Real.exp_sum,Finset.prod_pow_eq_pow_sum,←Finset.mul_sum,
    B.prefixRegionRate_fullTime_coe]

lemma measurable_prefixBandLikelihood (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    (r : ℝ≥0) (N : ℕ) : Measurable (B.prefixBandLikelihood S r N) :=
  Finset.measurable_fun_prod _ (fun k _ =>
    (measurable_bandPoissonLikelihood (B.bandIntensity k) hS r).comp (measurable_pi_apply k))

lemma prefixRegionRate_le_full (B : CountableInstance) {S : Set Point} (hS : MeasurableSet S)
    (hFinite : (Model.Instance.uniformClock.prod B.intensity) S<⊤) (N : ℕ) :
    B.prefixRegionRate S N≤B.poissonRegionRate S := by
  have h := ENNReal.sum_le_tsum (f:=fun k => ProphetSecretary.Limiting.intensity (B.bandIntensity k) S) (Finset.range N)
  rw [←B.regionIntensity_eq_tsum hS] at h
  have hNN := ENNReal.toNNReal_mono hFinite.ne h
  simpa only [ENNReal.toNNReal_sum (fun _ _ => measure_ne_top _ _),prefixRegionRate,poissonRegionRate,countRate] using hNN

lemma prefixPointCount_le_full_ae (B : CountableInstance) {S : Set Point} (hS : MeasurableSet S)
    (hFinite : (Model.Instance.uniformClock.prod B.intensity) S<⊤) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, ∀ N : ℕ,
      (∑ k∈Finset.range N, pointCount S (ω k))≤bandPointCount S ω := by
  filter_upwards [B.finite_region_count_and_prefix_ae hS hFinite] with ω hω
  obtain ⟨K,hK⟩ := eventually_atTop.mp hω.2
  intro N
  rw [←hK (max K N) (le_max_left _ _)]
  exact Finset.sum_le_sum_of_subset (Finset.range_mono (le_max_right K N))

lemma prefixBandLikelihood_tendsto_ae (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) (r : ℝ≥0) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, Tendsto (fun N => B.prefixBandLikelihood S r N ω)
      atTop (𝓝 (B.bandScalingLikelihood S r ω)) := by
  have hRegion := B.fullTime_region_finite hFinite
  have hRate := NNReal.tendsto_coe.2 (B.prefixRegionRate_tendsto (MeasurableSet.univ.prod hS) hRegion)
  have hRate' : Tendsto (fun N => (B.prefixRegionRate (univ ×ˢ S) N : ℝ)) atTop (𝓝 (B.intensity.real S)) := by
    simpa only [poissonRegionRate,Measure.real,Measure.prod_prod,measure_univ,one_mul,ENNReal.coe_toNNReal_eq_toReal] using hRate
  filter_upwards [B.finite_region_count_and_prefix_ae (MeasurableSet.univ.prod hS) hRegion] with ω hω
  have hCount : Tendsto (fun N => (r : ℝ)^(∑ k∈Finset.range N, pointCount (univ ×ˢ S) (ω k))) atTop
      (𝓝 ((r : ℝ)^bandPointCount (univ ×ˢ S) ω)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hω.2] with N hN
    rw [hN]
  have hExp := Real.continuous_exp.continuousAt.tendsto.comp (hRate'.const_mul (1-(r : ℝ)))
  simpa only [B.prefixBandLikelihood_eq hS r,bandScalingLikelihood,Function.comp_def] using hExp.mul hCount

lemma integrable_bandScalingLikelihood_of_finite (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) (r : ℝ≥0) :
    Integrable (B.bandScalingLikelihood S r) B.bandConfigurationsLaw := by
  have hCount := B.bandPointCount_hasLaw_of_finite_region (MeasurableSet.univ.prod hS) (B.fullTime_region_finite hFinite)
  have hGeo := hCount.measurePreserving (measurable_bandPointCount (MeasurableSet.univ.prod hS))
  have hInt := hGeo.integrable_comp_of_integrable
    (ProphetSecretary.Probability.integrable_poisson_geometric_zero (B.poissonRegionRate (univ ×ˢ S)) r)
  exact hInt.const_mul _

noncomputable def bandLikelihoodEnvelope (B : CountableInstance) (S : Set ℝ) (r : ℝ≥0)
    (ω : BandConfigurations) : ℝ :=
  Real.exp (B.intensity.real S)*(1+(r : ℝ)^bandPointCount (univ ×ˢ S) ω)

lemma integrable_bandLikelihoodEnvelope (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) (r : ℝ≥0) :
    Integrable (B.bandLikelihoodEnvelope S r) B.bandConfigurationsLaw := by
  have hCount := B.bandPointCount_hasLaw_of_finite_region (MeasurableSet.univ.prod hS) (B.fullTime_region_finite hFinite)
  have hInt := (hCount.measurePreserving (measurable_bandPointCount (MeasurableSet.univ.prod hS))).integrable_comp_of_integrable
    (ProphetSecretary.Probability.integrable_poisson_geometric_zero (B.poissonRegionRate (univ ×ˢ S)) r)
  exact ((integrable_const (1 : ℝ)).add hInt).const_mul _

lemma prefixBandLikelihood_le_envelope_ae (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) (r : ℝ≥0) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, ∀ N : ℕ,
      B.prefixBandLikelihood S r N ω≤B.bandLikelihoodEnvelope S r ω := by
  have hRegion := B.fullTime_region_finite hFinite
  filter_upwards [B.prefixPointCount_le_full_ae (MeasurableSet.univ.prod hS) hRegion] with ω hω
  intro N
  have hRateNN := B.prefixRegionRate_le_full (MeasurableSet.univ.prod hS) hRegion N
  have hRate : (B.prefixRegionRate (univ ×ˢ S) N : ℝ)≤B.intensity.real S := by
    have hReal : (B.prefixRegionRate (univ ×ˢ S) N : ℝ)≤(B.poissonRegionRate (univ ×ˢ S) : ℝ) := by exact_mod_cast hRateNN
    simpa only [poissonRegionRate,Measure.real,Measure.prod_prod,measure_univ,one_mul,ENNReal.coe_toNNReal_eq_toReal] using hReal
  have hRate0 := (B.prefixRegionRate (univ ×ˢ S) N).coe_nonneg
  have hExp : Real.exp ((1-(r : ℝ))*(B.prefixRegionRate (univ ×ˢ S) N : ℝ))≤Real.exp (B.intensity.real S) := by
    apply Real.exp_le_exp.mpr
    nlinarith only [hRate,mul_nonneg r.coe_nonneg hRate0]
  have hPow : (r : ℝ)^(∑ k∈Finset.range N, pointCount (univ ×ˢ S) (ω k))≤
      1+(r : ℝ)^bandPointCount (univ ×ˢ S) ω := by
    by_cases hr : (r : ℝ)≤1
    · exact (pow_le_one₀ r.coe_nonneg hr).trans (le_add_of_nonneg_right (pow_nonneg r.coe_nonneg _))
    · exact (pow_le_pow_right₀ (le_of_not_ge hr) (hω N)).trans (le_add_of_nonneg_left zero_le_one)
  rw [B.prefixBandLikelihood_eq hS r]
  exact mul_le_mul hExp hPow (pow_nonneg r.coe_nonneg _) (Real.exp_pos _).le

noncomputable def bandPrefixLaw (B : CountableInstance) (S : Set ℝ) (r : ℝ≥0) (N : ℕ) : Measure BandConfigurations :=
  Measure.infinitePi (fun k => if k∈Finset.range N then
    configurationLaw ((B.scaleBand S r).bandIntensity k) else configurationLaw (B.bandIntensity k))

lemma bandPrefixLaw_withDensity (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {r : ℝ≥0} (hr : 0<r) (N : ℕ) :
    B.bandPrefixLaw S r N=B.bandConfigurationsLaw.withDensity
      (fun ω => ENNReal.ofReal (B.prefixBandLikelihood S r N ω)) := by
  let μ := fun k => configurationLaw (B.bandIntensity k)
  let f := fun k ω => ENNReal.ofReal (bandPoissonLikelihood (B.bandIntensity k) S r ω)
  have hf (k : ℕ) : Measurable (f k) :=
    ENNReal.measurable_ofReal.comp (measurable_bandPoissonLikelihood (B.bandIntensity k) hS r)
  haveI (k : ℕ) : IsProbabilityMeasure ((μ k).withDensity (f k)) := by
    change IsProbabilityMeasure ((configurationLaw (B.bandIntensity k)).withDensity
      (fun ω => ENNReal.ofReal (bandPoissonLikelihood (B.bandIntensity k) S r ω)))
    rw [←configurationLaw_bandScaled_withDensity (B.bandIntensity k) hS hr]
    infer_instance
  have hFamily : (fun k => if k∈Finset.range N then configurationLaw ((B.scaleBand S r).bandIntensity k)
      else configurationLaw (B.bandIntensity k))=
      fun k => if k∈Finset.range N then (μ k).withDensity (f k) else μ k := by
    funext k
    by_cases hk : k∈Finset.range N
    · simp only [if_pos hk,B.scaleBand_bandIntensity hS r]
      exact configurationLaw_bandScaled_withDensity (B.bandIntensity k) hS hr
    · simp only [if_neg hk,μ]
  change Measure.infinitePi _=(Measure.infinitePi μ).withDensity _
  rw [hFamily,ProphetSecretary.Probability.infinitePi_finite_withDensity μ f hf (Finset.range N)]
  apply withDensity_congr_ae
  exact Eventually.of_forall (fun ω => (ENNReal.ofReal_prod_of_nonneg
    (fun k _ => by unfold bandPoissonLikelihood;positivity)).symm)

lemma bandPrefixLaw_apply_tendsto (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) {r : ℝ≥0} (hr : 0<r)
    {E : Set BandConfigurations} (hE : MeasurableSet E) :
    Tendsto (fun N => B.bandPrefixLaw S r N E) atTop
      (𝓝 (B.bandConfigurationsLaw.withDensity (fun ω => ENNReal.ofReal (B.bandScalingLikelihood S r ω)) E)) := by
  let D := B.bandLikelihoodEnvelope S r
  have hD : Integrable D (B.bandConfigurationsLaw.restrict E) := (B.integrable_bandLikelihoodEnvelope hS hFinite r).restrict
  have hD0 : ∀ᵐ ω ∂B.bandConfigurationsLaw.restrict E, 0≤D ω :=
    Eventually.of_forall (fun ω => by dsimp only [D,bandLikelihoodEnvelope];positivity)
  have hFin : (∫⁻ ω, ENNReal.ofReal (D ω) ∂B.bandConfigurationsLaw.restrict E)≠⊤ := by
    rw [←ofReal_integral_eq_lintegral_ofReal hD hD0]
    exact ENNReal.ofReal_ne_top
  have hBound (N : ℕ) : ∀ᵐ ω ∂B.bandConfigurationsLaw.restrict E,
      ENNReal.ofReal (B.prefixBandLikelihood S r N ω)≤ENNReal.ofReal (D ω) :=
    ae_restrict_of_ae ((B.prefixBandLikelihood_le_envelope_ae hS hFinite r).mono
      (fun ω hω => ENNReal.ofReal_le_ofReal (hω N)))
  have hLimit : ∀ᵐ ω ∂B.bandConfigurationsLaw.restrict E,
      Tendsto (fun N => ENNReal.ofReal (B.prefixBandLikelihood S r N ω)) atTop
        (𝓝 (ENNReal.ofReal (B.bandScalingLikelihood S r ω))) :=
    ae_restrict_of_ae ((B.prefixBandLikelihood_tendsto_ae hS hFinite r).mono
      (fun ω hω => (ENNReal.continuous_ofReal.tendsto _).comp hω))
  have hDCT := tendsto_lintegral_of_dominated_convergence (fun ω => ENNReal.ofReal (D ω))
    (fun N => ENNReal.measurable_ofReal.comp (B.measurable_prefixBandLikelihood hS r N)) hBound hFin hLimit
  simpa only [B.bandPrefixLaw_withDensity hS hr,withDensity_apply _ hE,Function.comp_def] using hDCT

/-- The actual complete cloud likelihood for every measurable finite-intensity set. -/
theorem bandConfigurationsLaw_scaleBand_withDensity_of_finite (B : CountableInstance)
    {S : Set ℝ} (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) {r : ℝ≥0} (hr : 0<r) :
    (B.scaleBand S r).bandConfigurationsLaw=B.bandConfigurationsLaw.withDensity
      (fun ω => ENNReal.ofReal (B.bandScalingLikelihood S r ω)) := by
  symm
  change _=Measure.infinitePi (fun k => configurationLaw ((B.scaleBand S r).bandIntensity k))
  apply Measure.eq_infinitePi
  intro s t ht
  have hE : MeasurableSet (Set.pi (s : Set ℕ) t) :=
    MeasurableSet.pi s.countable_toSet (fun k _ => ht k)
  have hLimit := B.bandPrefixLaw_apply_tendsto hS hFinite hr hE
  obtain ⟨K,hK⟩ := Finset.exists_nat_subset_range s
  have hEventually : (fun N => B.bandPrefixLaw S r N (Set.pi (s : Set ℕ) t)) =ᶠ[atTop]
      (fun _ => ∏ k∈s, configurationLaw ((B.scaleBand S r).bandIntensity k) (t k)) := by
    apply eventually_atTop.mpr
    refine ⟨K,fun N hN => ?_⟩
    dsimp only
    unfold bandPrefixLaw
    rw [Measure.infinitePi_pi _ (fun k _ => ht k)]
    apply Finset.prod_congr rfl
    intro k hk
    have hkN : k∈Finset.range N := (Finset.range_mono hN) (hK hk)
    rw [if_pos hkN]
  have hConst : Tendsto (fun N => B.bandPrefixLaw S r N (Set.pi (s : Set ℕ) t)) atTop
      (𝓝 (∏ k∈s, configurationLaw ((B.scaleBand S r).bandIntensity k) (t k))) :=
    tendsto_const_nhds.congr' hEventually.symm
  exact tendsto_nhds_unique hLimit hConst

/-- Offers, clocks, and the arbitrary independent policy seed keep their actual
product law when the finite-band cloud likelihood is applied. -/
theorem completeWorldLaw_scaleBand_withDensity_of_finite (B : CountableInstance)
    {S : Set ℝ} (hS : MeasurableSet S) (hFinite : B.intensity S<⊤) {r : ℝ≥0} (hr : 0<r)
    {Seed : Type*} [MeasurableSpace Seed] (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.scaleBand S r).completeWorldLaw ν=(B.completeWorldLaw ν).withDensity
      (fun v => ENNReal.ofReal (B.bandScalingLikelihood S r v.1)) := by
  have hDensity : Measurable (fun ω => ENNReal.ofReal (B.bandScalingLikelihood S r ω)) :=
    ENNReal.measurable_ofReal.comp (B.measurable_bandScalingLikelihood hS r)
  change (B.scaleBand S r).bandConfigurationsLaw.prod (B.individualWorldLaw ν)=_
  rw [B.bandConfigurationsLaw_scaleBand_withDensity_of_finite hS hFinite hr]
  exact prod_withDensity_left hDensity

end ProphetSecretary.Limiting.CountableInstance
