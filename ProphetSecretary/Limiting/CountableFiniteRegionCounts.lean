import ProphetSecretary.Limiting.CountablePoissonCounts
import ProphetSecretary.Analysis.PoissonMixtureLimit
import Mathlib.MeasureTheory.OuterMeasure.BorelCantelli

/-!
# Counts in arbitrary finite-intensity regions

A region of finite intensity may meet infinitely many construction bands.
The Poisson first moment and Borel--Cantelli show that only finitely many
bands contribute almost surely. The count is the actual counting-measure
mass, including all arrivals after a stopping policy has stopped.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators NNReal ENNReal Topology
namespace ProphetSecretary.Limiting
namespace CountableInstance

lemma regionIntensity_eq_tsum (B : CountableInstance) {S : Set Point} (hS : MeasurableSet S) :
    (Model.Instance.uniformClock.prod B.intensity) S=
      ∑' k, ProphetSecretary.Limiting.intensity (B.bandIntensity k) S := by
  rw [←B.sum_bandIntensity,Measure.prod_sum_right,Measure.sum_apply _ hS]
  rfl

lemma bandPointCount_nonzero_measure_le (B : CountableInstance) {S : Set Point}
    (hS : MeasurableSet S) (k : ℕ) :
    B.bandConfigurationsLaw {ω | pointCount S (ω k)≠0}≤
      ProphetSecretary.Limiting.intensity (B.bandIntensity k) S := by
  have hLaw := (pointCount_measurePreserving (B.bandIntensity k) hS).comp (B.bandConfiguration_measurePreserving k)
  have hM : MeasurableSet {j : ℕ | j≠0} := by measurability
  have hProb := hLaw.measure_preimage hM.nullMeasurableSet
  simp only [Function.comp_def] at hProb
  change B.bandConfigurationsLaw ((fun ω => pointCount S (ω k)) ⁻¹' {j : ℕ | j≠0})≤_
  rw [hProb]
  calc
    _ = ∫⁻ j : ℕ, ({j : ℕ | j≠0}.indicator (fun _ => (1 : ℝ≥0∞))) j
        ∂poissonMeasure (countRate (B.bandIntensity k) S) := (lintegral_indicator_one hM).symm
    _ ≤ ∫⁻ j : ℕ, (j : ℝ≥0∞) ∂poissonMeasure (countRate (B.bandIntensity k) S) := by
      apply lintegral_mono
      intro j
      cases j with
      | zero => simp
      | succ j =>
          rw [Set.indicator_of_mem (show j+1∈{j : ℕ | j≠0} from Nat.succ_ne_zero j)]
          rw [Nat.cast_add,Nat.cast_one]
          exact le_add_self
    _ = (countRate (B.bandIntensity k) S : ℝ≥0∞) := lintegral_poisson_first _
    _ = _ := by simp only [countRate,ENNReal.coe_toNNReal (measure_ne_top _ _)]

lemma finite_contributing_bands_ae (B : CountableInstance) {S : Set Point}
    (hS : MeasurableSet S) (hFinite : (Model.Instance.uniformClock.prod B.intensity) S<⊤) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, {k | pointCount S (ω k)≠0}.Finite := by
  apply ae_finite_setOf_mem
  apply ne_top_of_le_ne_top hFinite.ne
  calc
    _ ≤ ∑' k, ProphetSecretary.Limiting.intensity (B.bandIntensity k) S :=
      ENNReal.tsum_le_tsum (fun k => B.bandPointCount_nonzero_measure_le hS k)
    _ = _ := (B.regionIntensity_eq_tsum hS).symm

lemma count_eq_prefix_of_finite_support {S : Set Point} (hS : MeasurableSet S)
    (ω : BandConfigurations) (hFinite : {k | pointCount S (ω k)≠0}.Finite) :
    ∃ K : ℕ, ∀ N, K≤N →
      bandCountingMeasure ω S=(∑ k∈Finset.range N, pointCount S (ω k) : ℕ) ∧
      bandPointCount S ω=∑ k∈Finset.range N, pointCount S (ω k) := by
  obtain ⟨K,hK⟩ := hFinite.bddAbove
  refine ⟨K+1,fun N hN => ?_⟩
  have hz (k : ℕ) (hk : k∉Finset.range N) : pointCount S (ω k)=0 := by
    by_contra hNe
    have hkK := hK hNe
    have hkN : N≤k := by simpa only [Finset.mem_range,not_lt] using hk
    omega
  have hMass : bandCountingMeasure ω S=(∑ k∈Finset.range N, pointCount S (ω k) : ℕ) := by
    rw [bandCountingMeasure,Measure.sum_apply _ hS]
    simp_rw [countingMeasure_eq_pointCount hS]
    rw [tsum_eq_sum (fun k hk => by rw [hz k hk,Nat.cast_zero])]
    simp only [Nat.cast_sum]
  refine ⟨hMass,?_⟩
  unfold bandPointCount Measure.real
  rw [hMass,ENNReal.toReal_natCast,Nat.floor_natCast]

lemma finite_region_count_and_prefix_ae (B : CountableInstance) {S : Set Point}
    (hS : MeasurableSet S) (hFinite : (Model.Instance.uniformClock.prod B.intensity) S<⊤) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw,
      bandCountingMeasure ω S=(bandPointCount S ω : ℝ≥0∞) ∧
        ∀ᶠ N in atTop, (∑ k∈Finset.range N, pointCount S (ω k))=bandPointCount S ω := by
  filter_upwards [B.finite_contributing_bands_ae hS hFinite] with ω hω
  obtain ⟨K,hK⟩ := count_eq_prefix_of_finite_support hS ω hω
  refine ⟨?_,eventually_atTop.mpr ⟨K,fun N hN => (hK N hN).2.symm⟩⟩
  rw [(hK K le_rfl).1,(hK K le_rfl).2]

noncomputable def prefixRegionRate (B : CountableInstance) (S : Set Point) (N : ℕ) : ℝ≥0 :=
  ∑ k∈Finset.range N, countRate (B.bandIntensity k) S

lemma prefixRegionRate_tendsto (B : CountableInstance) {S : Set Point}
    (hS : MeasurableSet S) (hFinite : (Model.Instance.uniformClock.prod B.intensity) S<⊤) :
    Tendsto (B.prefixRegionRate S) atTop (𝓝 (B.poissonRegionRate S)) := by
  have hENN := ENNReal.tendsto_nat_tsum (fun k => ProphetSecretary.Limiting.intensity (B.bandIntensity k) S)
  rw [←B.regionIntensity_eq_tsum hS] at hENN
  have h := (ENNReal.tendsto_toNNReal hFinite.ne).comp hENN
  change Tendsto (fun N => ∑ k∈Finset.range N, (ProphetSecretary.Limiting.intensity (B.bandIntensity k) S).toNNReal)
    atTop (𝓝 ((Model.Instance.uniformClock.prod B.intensity) S).toNNReal)
  simpa only [Function.comp_def,ENNReal.toNNReal_sum (fun _ _ => measure_ne_top _ _)] using h

lemma prefixRegionCount_hasLaw (B : CountableInstance) {S : Set Point} (hS : MeasurableSet S) (N : ℕ) :
    HasLaw (fun ω => ∑ k∈Finset.range N, pointCount S (ω k))
      (poissonMeasure (B.prefixRegionRate S N)) B.bandConfigurationsLaw := by
  have hI : iIndepFun (fun k ω => pointCount S (ω k)) B.bandConfigurationsLaw :=
    B.bandConfigurations_independent.comp (fun _ => pointCount S) (fun _ => measurable_pointCount hS)
  have hX (k) : HasLaw (fun ω => pointCount S (ω k))
      (poissonMeasure (countRate (B.bandIntensity k) S)) B.bandConfigurationsLaw :=
    (pointCount_measurePreserving (B.bandIntensity k) hS).hasLaw.fun_comp (B.bandConfiguration_measurePreserving k).hasLaw
  exact ProphetSecretary.Probability.hasLaw_finsetSum_poisson hI hX (Finset.range N)

/-- Exact Poisson law for every measurable region of finite total intensity. -/
theorem bandPointCount_hasLaw_of_finite_region (B : CountableInstance) {S : Set Point}
    (hS : MeasurableSet S) (hFinite : (Model.Instance.uniformClock.prod B.intensity) S<⊤) :
    HasLaw (bandPointCount S) (poissonMeasure (B.poissonRegionRate S)) B.bandConfigurationsLaw := by
  have hMeas := measurable_bandPointCount hS
  refine ⟨hMeas.aemeasurable,?_⟩
  apply Measure.ext_of_singleton
  intro j
  let f : ℕ → BandConfigurations → ℝ := fun N =>
    {ω | (∑ k∈Finset.range N, pointCount S (ω k))=j}.indicator (fun _ => 1)
  let g : BandConfigurations → ℝ := {ω | bandPointCount S ω=j}.indicator (fun _ => 1)
  have hSet (N : ℕ) : MeasurableSet {ω : BandConfigurations | (∑ k∈Finset.range N, pointCount S (ω k))=j} := by
    have hm : Measurable (fun ω : BandConfigurations => ∑ k∈Finset.range N, pointCount S (ω k)) :=
      Finset.measurable_fun_sum _ (fun k _ => (measurable_pointCount hS).comp (measurable_pi_apply k))
    exact measurableSet_eq_fun hm measurable_const
  have hSetG : MeasurableSet {ω : BandConfigurations | bandPointCount S ω=j} :=
    measurableSet_eq_fun hMeas measurable_const
  have hF (N : ℕ) : Measurable (f N) := measurable_const.indicator (hSet N)
  have hBound (N : ℕ) : ∀ᵐ ω ∂B.bandConfigurationsLaw, ‖f N ω‖≤1 :=
    Eventually.of_forall (fun ω => by simp only [f,Set.indicator_apply];split_ifs <;> norm_num)
  have hLim : ∀ᵐ ω ∂B.bandConfigurationsLaw, Tendsto (fun N => f N ω) atTop (𝓝 (g ω)) := by
    filter_upwards [B.finite_region_count_and_prefix_ae hS hFinite] with ω hω
    apply tendsto_const_nhds.congr'
    filter_upwards [hω.2] with N hN
    simp only [f,g,Set.indicator_apply,Set.mem_setOf_eq,hN]
  have hDCT := tendsto_integral_filter_of_dominated_convergence (fun _ : BandConfigurations => (1 : ℝ))
    (Eventually.of_forall (fun N => (hF N).aestronglyMeasurable))
    (Eventually.of_forall hBound) (integrable_const _) hLim
  have hMean (N : ℕ) : (∫ ω, f N ω ∂B.bandConfigurationsLaw)=
      ProphetSecretary.Limiting.poissonWeight (B.prefixRegionRate S N) j := by
    rw [show (∫ ω, f N ω ∂B.bandConfigurationsLaw)=
      B.bandConfigurationsLaw.real {ω | (∑ k∈Finset.range N, pointCount S (ω k))=j}
      from integral_indicator_one (hSet N)]
    have h := (B.prefixRegionCount_hasLaw hS N).measureReal_eq (p:=fun i => i=j) (by measurability)
    simpa only [Set.setOf_eq_eq_singleton,poissonMeasure_real_singleton,poissonWeight] using h
  have hMeanG : (∫ ω, g ω ∂B.bandConfigurationsLaw)=B.bandConfigurationsLaw.real {ω | bandPointCount S ω=j} :=
    integral_indicator_one hSetG
  simp_rw [hMean,hMeanG] at hDCT
  have hProb := tendsto_nhds_unique hDCT
    (ProphetSecretary.Analysis.poissonWeight_tendsto (B.prefixRegionRate_tendsto hS hFinite) j)
  have hReal : (B.bandConfigurationsLaw.map (bandPointCount S)).real {j}=
      (poissonMeasure (B.poissonRegionRate S)).real {j} := by
    rw [map_measureReal_apply hMeas (measurableSet_singleton j),poissonMeasure_real_singleton]
    exact hProb
  calc
    _ = ENNReal.ofReal ((B.bandConfigurationsLaw.map (bandPointCount S)).real {j}) := (ofReal_measureReal (measure_ne_top _ _)).symm
    _ = ENNReal.ofReal ((poissonMeasure (B.poissonRegionRate S)).real {j}) := congrArg ENNReal.ofReal hReal
    _ = _ := ofReal_measureReal (measure_ne_top _ _)

end CountableInstance
end ProphetSecretary.Limiting
