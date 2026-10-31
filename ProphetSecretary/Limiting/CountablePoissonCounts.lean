import ProphetSecretary.Limiting.CountableVoid
import ProphetSecretary.Limiting.PoissonDisjointCounts
import ProphetSecretary.Probability.PoissonFiniteSum
import Mathlib.MeasureTheory.Function.Floor

/-!
# Actual counts above the reserve in the countable Poisson construction

The sum of the actual finite counting measures is measurable. Above any
strictly larger mark cutoff, only finitely many construction bands contribute.
Their actual independent Poisson counts determine the total count law.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical NNReal ENNReal BigOperators

namespace ProphetSecretary.Limiting

noncomputable def bandCountingMeasure (ω : CountableInstance.BandConfigurations) : Measure Point :=
  Measure.sum (fun k => countingMeasure (ω k))

lemma measurable_bandCountingMeasure : Measurable bandCountingMeasure := by
  apply Measure.measurable_of_measurable_coe
  intro S hS
  have he : (fun ω => bandCountingMeasure ω S) = fun ω => ∑' k, countingMeasure (ω k) S := by
    funext ω
    exact Measure.sum_apply _ hS
  rw [he]
  exact Measurable.tsum (fun k => (Measure.measurable_coe hS).comp
    (measurable_countingMeasure.comp (measurable_pi_apply k)))

/-- A total measurable natural count; its defining mass is finite and integral
almost surely for the regions above the reserve considered below. -/
noncomputable def bandPointCount (S : Set Point) (ω : CountableInstance.BandConfigurations) : ℕ :=
  Nat.floor ((bandCountingMeasure ω).real S)

lemma measurable_bandPointCount {S : Set Point} (hS : MeasurableSet S) : Measurable (bandPointCount S) :=
  Nat.measurable_floor.comp (((Measure.measurable_coe hS).comp measurable_bandCountingMeasure).ennreal_toReal)

namespace CountableInstance

variable (B : CountableInstance)

lemma bandCountingMeasure_region_eq_sum {b : ℝ} {K : ℕ} {S : Set Point}
    (hS : MeasurableSet S) (hsub : S ⊆ univ ×ˢ Ioi b)
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw,
      bandCountingMeasure ω S = ∑ k ∈ Finset.range (K+1), (pointCount S (ω k) : ℝ≥0∞) := by
  filter_upwards [B.bandConfigurations_marks_in_band] with ω hω
  have hz (k : ℕ) (hk : k ∉ Finset.range (K+1)) : countingMeasure (ω k) S = 0 := by
    have hkg : K < k := by simp only [Finset.mem_range,not_lt] at hk; omega
    rw [countingMeasure_eq_pointCount hS]
    have hn : pointCount S (ω k) = 0 := by
      unfold pointCount
      apply Finset.sum_eq_zero
      intro j _
      apply if_neg
      intro hj
      exact (not_lt_of_ge (hK k hkg _ (hω k j))) (hsub hj).2
    rw [hn,Nat.cast_zero]
  rw [bandCountingMeasure,Measure.sum_apply _ hS,tsum_eq_sum hz]
  exact Finset.sum_congr rfl (fun k _ => countingMeasure_eq_pointCount hS (ω k))

lemma bandPointCount_region_eq_sum {b : ℝ} {K : ℕ} {S : Set Point}
    (hS : MeasurableSet S) (hsub : S ⊆ univ ×ˢ Ioi b)
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw,
      bandPointCount S ω = ∑ k ∈ Finset.range (K+1), pointCount S (ω k) := by
  filter_upwards [B.bandCountingMeasure_region_eq_sum hS hsub hK] with ω hω
  unfold bandPointCount Measure.real
  rw [hω,← Nat.cast_sum,ENNReal.toReal_natCast,Nat.floor_natCast]

lemma poisson_intensity_region_eq_sum {b : ℝ} {K : ℕ} {S : Set Point}
    (hS : MeasurableSet S) (hsub : S ⊆ univ ×ˢ Ioi b)
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) :
    (Model.Instance.uniformClock.prod B.intensity) S =
      ∑ k ∈ Finset.range (K+1), ProphetSecretary.Limiting.intensity (B.bandIntensity k) S := by
  have hz (k : ℕ) (hk : k ∉ Finset.range (K+1)) : ProphetSecretary.Limiting.intensity (B.bandIntensity k) S = 0 := by
    have hkg : K < k := by simp only [Finset.mem_range,not_lt] at hk; omega
    apply measure_mono_null hsub
    simp only [ProphetSecretary.Limiting.intensity,Measure.prod_prod,B.bandIntensity_tail_zero hK k hkg,mul_zero]
  rw [← B.sum_bandIntensity,Measure.prod_sum_right,Measure.sum_apply _ hS]
  change (∑' k, ProphetSecretary.Limiting.intensity (B.bandIntensity k) S) = _
  exact tsum_eq_sum hz

noncomputable def poissonRegionRate (S : Set Point) : ℝ≥0 :=
  ((Model.Instance.uniformClock.prod B.intensity) S).toNNReal

lemma poissonRegionRate_eq_sum {b : ℝ} {K : ℕ} {S : Set Point}
    (hS : MeasurableSet S) (hsub : S ⊆ univ ×ˢ Ioi b)
    (hK : ∀ k, K < k → ∀ x ∈ B.markBand k, x ≤ b) :
    B.poissonRegionRate S = ∑ k ∈ Finset.range (K+1), countRate (B.bandIntensity k) S := by
  unfold poissonRegionRate
  rw [B.poisson_intensity_region_eq_sum hS hsub hK,ENNReal.toNNReal_sum (fun _ _ => measure_ne_top _ _)]
  rfl

/-- Exact Poisson count law on every measurable region above any b>a. -/
theorem bandPointCount_hasLaw {b : ℝ} (hb : (B.terminal : ℝ) < b) {S : Set Point}
    (hS : MeasurableSet S) (hsub : S ⊆ univ ×ˢ Ioi b) :
    HasLaw (bandPointCount S) (poissonMeasure (B.poissonRegionRate S)) B.bandConfigurationsLaw := by
  obtain ⟨K,hK⟩ := B.eventually_bands_below hb
  have hI : iIndepFun (fun k ω => pointCount S (ω k)) B.bandConfigurationsLaw :=
    B.bandConfigurations_independent.comp (fun _ => pointCount S) (fun _ => measurable_pointCount hS)
  have hX (k) : HasLaw (fun ω => pointCount S (ω k))
      (poissonMeasure (countRate (B.bandIntensity k) S)) B.bandConfigurationsLaw :=
    (pointCount_measurePreserving (B.bandIntensity k) hS).hasLaw.fun_comp
      (B.bandConfiguration_measurePreserving k).hasLaw
  rw [B.poissonRegionRate_eq_sum hS hsub hK]
  exact (ProphetSecretary.Probability.hasLaw_finsetSum_poisson hI hX (Finset.range (K+1))).congr
    (B.bandPointCount_region_eq_sum hS hsub hK)

/-- The natural count is the actual integer-valued counting-measure mass,
not merely a floor with a distributional interpretation. -/
lemma bandCountingMeasure_eq_natCount_ae {b : ℝ} (hb : (B.terminal : ℝ) < b) {S : Set Point}
    (hS : MeasurableSet S) (hsub : S ⊆ univ ×ˢ Ioi b) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, bandCountingMeasure ω S = (bandPointCount S ω : ℝ≥0∞) := by
  obtain ⟨K,hK⟩ := B.eventually_bands_below hb
  filter_upwards [B.bandCountingMeasure_region_eq_sum hS hsub hK,
    B.bandPointCount_region_eq_sum hS hsub hK] with ω hm hn
  rw [hm,hn,Nat.cast_sum]

lemma bandCountingMeasure_region_finite_ae {b : ℝ} (hb : (B.terminal : ℝ) < b) {S : Set Point}
    (hS : MeasurableSet S) (hsub : S ⊆ univ ×ˢ Ioi b) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, bandCountingMeasure ω S < ⊤ := by
  filter_upwards [B.bandCountingMeasure_eq_natCount_ae hb hS hsub] with ω hω
  rw [hω]
  exact (ENNReal.natCast_ne_top _).lt_top

lemma bandPointCount_measurePreserving {b : ℝ} (hb : (B.terminal : ℝ) < b) {S : Set Point}
    (hS : MeasurableSet S) (hsub : S ⊆ univ ×ˢ Ioi b) :
    MeasurePreserving (bandPointCount S) B.bandConfigurationsLaw (poissonMeasure (B.poissonRegionRate S)) :=
  (B.bandPointCount_hasLaw hb hS hsub).measurePreserving (measurable_bandPointCount hS)

end CountableInstance
end ProphetSecretary.Limiting
