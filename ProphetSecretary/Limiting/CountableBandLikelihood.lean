import ProphetSecretary.Limiting.CountableBandScaling
import ProphetSecretary.Limiting.FiniteBandNull
import ProphetSecretary.Limiting.CountablePoissonCounts
import ProphetSecretary.Limiting.BandGeneratingFunctional
import ProphetSecretary.Limiting.CountableObservations
import ProphetSecretary.Probability.InfiniteFiniteDensity

/-!
# Actual likelihood for a band bounded away from the reserve

Only finitely many construction bands can contain affected marks. Their
actual independent laws give the complete band-count likelihood. The final
count includes all points, including those after stopping, and is analytical.
No construction-band label or future count is supplied to any callback.
-/

open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

noncomputable def bandScalingLikelihood (B : CountableInstance) (S : Set ℝ) (r : ℝ≥0)
    (ω : BandConfigurations) : ℝ :=
  Real.exp ((1-(r : ℝ))*B.intensity.real S)*(r : ℝ)^(bandPointCount (univ ×ˢ S) ω)

lemma measurable_bandScalingLikelihood (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) (r : ℝ≥0) : Measurable (B.bandScalingLikelihood S r) :=
  ((measurable_of_countable (fun N : ℕ => (r : ℝ)^N)).comp
    (measurable_bandPointCount (MeasurableSet.univ.prod hS))).const_mul _

lemma bandIntensity_set_null_of_below (B : CountableInstance) {S : Set ℝ} {b : ℝ}
    (hSub : S ⊆ Ioi b) {K : ℕ}
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) (k : ℕ) (hk : K < k) :
    (B.bandIntensity k : Measure ℝ) S=0 :=
  measure_mono_null hSub (B.bandIntensity_tail_zero hK k hk)

lemma bandMarkRate_eq_prefix (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hSub : S ⊆ Ioi b) {K : ℕ}
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) :
    (∑ k ∈ Finset.range (K+1), (B.bandIntensity k S : ℝ))=B.intensity.real S := by
  have hENN := B.poisson_intensity_region_eq_sum (MeasurableSet.univ.prod hS)
    (fun p hp => ⟨hp.1,hSub hp.2⟩) hK
  simp only [ProphetSecretary.Limiting.intensity,Measure.prod_prod,measure_univ,one_mul] at hENN
  have hReal := congrArg ENNReal.toReal hENN
  rw [ENNReal.toReal_sum (fun _ _ => measure_ne_top _ _)] at hReal
  exact hReal.symm

lemma bandScalingLikelihood_eq_prefix (B : CountableInstance) {S : Set ℝ} (hS : MeasurableSet S)
    {b : ℝ} (hSub : S ⊆ Ioi b) {K : ℕ}
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) (r : ℝ≥0) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw,
      (∏ k ∈ Finset.range (K+1), ENNReal.ofReal (bandPoissonLikelihood (B.bandIntensity k) S r (ω k)))=
        ENNReal.ofReal (B.bandScalingLikelihood S r ω) := by
  have hRate := B.bandMarkRate_eq_prefix hS hSub hK
  filter_upwards [B.bandPointCount_region_eq_sum (MeasurableSet.univ.prod hS)
    (fun p hp => ⟨hp.1,hSub hp.2⟩) hK] with ω hCount
  have hReal : (∏ k ∈ Finset.range (K+1), bandPoissonLikelihood (B.bandIntensity k) S r (ω k))=
      B.bandScalingLikelihood S r ω := by
    calc
      _ = ∏ k ∈ Finset.range (K+1), Real.exp ((1-(r : ℝ))*(B.bandIntensity k S : ℝ))*
          (r : ℝ)^(pointCount (univ ×ˢ S) (ω k)) := by
        apply Finset.prod_congr rfl
        intro k _
        exact bandPoissonLikelihood_eq (B.bandIntensity k) hS r (ω k)
      _ = Real.exp ((1-(r : ℝ))*(∑ k ∈ Finset.range (K+1), (B.bandIntensity k S : ℝ)))*
          (r : ℝ)^(∑ k ∈ Finset.range (K+1), pointCount (univ ×ˢ S) (ω k)) := by
        rw [Finset.prod_mul_distrib,← Real.exp_sum,Finset.prod_pow_eq_pow_sum,← Finset.mul_sum]
      _ = _ := by rw [hRate,← hCount]; rfl
  calc
    _ = ENNReal.ofReal (∏ k ∈ Finset.range (K+1), bandPoissonLikelihood (B.bandIntensity k) S r (ω k)) :=
      (ENNReal.ofReal_prod_of_nonneg (fun k _ => by unfold bandPoissonLikelihood; positivity)).symm
    _ = _ := congrArg ENNReal.ofReal hReal

theorem bandConfigurationsLaw_scaleBand_withDensity (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b)
    {r : ℝ≥0} (hr : 0 < r) :
    (B.scaleBand S r).bandConfigurationsLaw=B.bandConfigurationsLaw.withDensity
      (fun ω => ENNReal.ofReal (B.bandScalingLikelihood S r ω)) := by
  obtain ⟨K,hK⟩ := B.eventually_bands_below hb
  let μ := fun k => configurationLaw (B.bandIntensity k)
  let f := fun k ω => ENNReal.ofReal (bandPoissonLikelihood (B.bandIntensity k) S r ω)
  have hf (k : ℕ) : Measurable (f k) :=
    ENNReal.measurable_ofReal.comp (measurable_bandPoissonLikelihood (B.bandIntensity k) hS r)
  haveI (k : ℕ) : IsProbabilityMeasure ((μ k).withDensity (f k)) := by
    change IsProbabilityMeasure ((configurationLaw (B.bandIntensity k)).withDensity
      (fun ω => ENNReal.ofReal (bandPoissonLikelihood (B.bandIntensity k) S r ω)))
    rw [← configurationLaw_bandScaled_withDensity (B.bandIntensity k) hS hr]
    infer_instance
  have hFamily : (fun k => configurationLaw ((B.scaleBand S r).bandIntensity k))=
      fun k => if k ∈ Finset.range (K+1) then (μ k).withDensity (f k) else μ k := by
    funext k
    rw [B.scaleBand_bandIntensity hS r k]
    by_cases hk : k ∈ Finset.range (K+1)
    · simpa only [if_pos hk,μ,f] using configurationLaw_bandScaled_withDensity (B.bandIntensity k) hS hr
    · have hk' : K < k := by simp only [Finset.mem_range,not_lt] at hk; omega
      simp only [if_neg hk,μ]
      rw [bandScaledIntensity_of_null (B.bandIntensity k) hS (B.bandIntensity_set_null_of_below hSub hK k hk') r]
  change Measure.infinitePi _=(Measure.infinitePi μ).withDensity _
  rw [hFamily,ProphetSecretary.Probability.infinitePi_finite_withDensity μ f hf (Finset.range (K+1))]
  exact withDensity_congr_ae (B.bandScalingLikelihood_eq_prefix hS hSub hK r)

/-- The full observation-world likelihood is derived from the actual independent
cloud and the unchanged individual/clock/auxiliary product law. -/
theorem completeWorldLaw_scaleBand_withDensity (B : CountableInstance) {S : Set ℝ}
    (hS : MeasurableSet S) {b : ℝ} (hb : (B.terminal : ℝ) < b) (hSub : S ⊆ Ioi b)
    {r : ℝ≥0} (hr : 0 < r) {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (B.scaleBand S r).completeWorldLaw ν=(B.completeWorldLaw ν).withDensity
      (fun v => ENNReal.ofReal (B.bandScalingLikelihood S r v.1)) := by
  have hDensity : Measurable (fun ω => ENNReal.ofReal (B.bandScalingLikelihood S r ω)) :=
    ENNReal.measurable_ofReal.comp (B.measurable_bandScalingLikelihood hS r)
  change (B.scaleBand S r).bandConfigurationsLaw.prod (B.individualWorldLaw ν)=_
  rw [B.bandConfigurationsLaw_scaleBand_withDensity hS hb hSub hr]
  exact prod_withDensity_left hDensity

end ProphetSecretary.Limiting.CountableInstance
