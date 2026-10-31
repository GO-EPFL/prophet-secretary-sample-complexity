import ProphetSecretary.Probability.CountableMeasureTests
import ProphetSecretary.Limiting.OmissionCloudLaw

/-!
# Countable observations separating the actual locally finite cloud measures

These coordinates are for analytical couplings, not inputs to an online
policy. Finiteness of each band is proved on the constructed laws, and values
remain ENNReal throughout, allowing infinite total mass near the reserve.
-/

open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting.CountableInstance

abbrev BandObservations := (ℕ × Finset ℕ) → ℝ≥0∞

noncomputable def bandObservations (B : CountableInstance) (μ : Measure Point) : BandObservations :=
  fun p => μ (ProphetSecretary.Probability.measureTest Point p.2 ∩ (univ ×ˢ B.markBand p.1))

lemma measurable_bandObservations (B : CountableInstance) : Measurable (bandObservations B) :=
  measurable_pi_lambda _ (fun p => Measure.measurable_coe
    ((ProphetSecretary.Probability.measurableSet_measureTest Point p.2).inter
      (MeasurableSet.univ.prod (B.measurableSet_markBand p.1))))

noncomputable def RegularBandMeasure (B : CountableInstance) (μ : Measure Point) : Prop :=
  μ (univ ×ˢ Iic (B.terminal : ℝ)) = 0 ∧ ∀ k, μ (univ ×ˢ B.markBand k) < ⊤

lemma measurableSet_regularBandMeasure (B : CountableInstance) :
    MeasurableSet {μ : Measure Point | RegularBandMeasure B μ} := by
  unfold RegularBandMeasure
  simp only [setOf_and,setOf_forall]
  exact (measurableSet_eq_fun (Measure.measurable_coe (MeasurableSet.univ.prod measurableSet_Iic))
    measurable_const).inter (MeasurableSet.iInter (fun k => measurableSet_lt
      (Measure.measurable_coe (MeasurableSet.univ.prod (B.measurableSet_markBand k))) measurable_const))

lemma bandCountingMeasure_regular_ae (B : CountableInstance) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, RegularBandMeasure B (bandCountingMeasure ω) := by
  have hband (k : ℕ) : ∀ᵐ ω ∂B.bandConfigurationsLaw,
      bandCountingMeasure ω (univ ×ˢ B.markBand k) < ⊤ :=
    B.bandCountingMeasure_region_finite_ae (B.terminal_lt_markCutoff k)
      (MeasurableSet.univ.prod (B.measurableSet_markBand k))
      (fun _ hp => ⟨hp.1,B.markBand_subset_tail k hp.2⟩)
  filter_upwards [B.bandCountingMeasure_below_reserve_zero_ae,ae_all_iff.mpr hband] with ω hzero hfinite
  exact ⟨hzero,hfinite⟩

lemma sum_restrict_bands_eq (B : CountableInstance) (μ : Measure Point)
    (hzero : μ (univ ×ˢ Iic (B.terminal : ℝ)) = 0) :
    Measure.sum (fun k => μ.restrict (univ ×ˢ B.markBand k)) = μ := by
  have hd : Pairwise (fun k l => Disjoint ((univ : Set ℝ) ×ˢ B.markBand k) ((univ : Set ℝ) ×ˢ B.markBand l)) := by
    intro k l hkl
    exact Set.disjoint_left.mpr (fun _ hp hq => Set.disjoint_left.mp (B.markBands_disjoint hkl) hp.2 hq.2)
  have hu : (⋃ k, (univ ×ˢ B.markBand k : Set Point)) = univ ×ˢ Ioi (B.terminal : ℝ) := by
    rw [← Set.prod_iUnion,B.iUnion_markBand]
  rw [← Measure.restrict_iUnion hd (fun k => MeasurableSet.univ.prod (B.measurableSet_markBand k)),hu]
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hzero] with p hp
  refine ⟨mem_univ _,?_⟩
  change (B.terminal : ℝ) < p.2
  simpa only [mem_prod,mem_univ,true_and,mem_Iic,not_le] using hp

lemma eq_of_bandObservations (B : CountableInstance) (μ ν : Measure Point)
    (hμ : RegularBandMeasure B μ) (hν : RegularBandMeasure B ν)
    (hobs : bandObservations B μ = bandObservations B ν) : μ = ν := by
  have hband (k : ℕ) : μ.restrict (univ ×ˢ B.markBand k) = ν.restrict (univ ×ˢ B.markBand k) := by
    letI : IsFiniteMeasure (μ.restrict (univ ×ˢ B.markBand k)) := ⟨by
      simpa only [Measure.restrict_apply_univ] using hμ.2 k⟩
    apply ProphetSecretary.Probability.finiteMeasure_eq_of_tests Point
    intro s
    rw [Measure.restrict_apply (ProphetSecretary.Probability.measurableSet_measureTest Point s),
      Measure.restrict_apply (ProphetSecretary.Probability.measurableSet_measureTest Point s)]
    exact congrFun hobs (k,s)
  calc
    μ = Measure.sum (fun k => μ.restrict (univ ×ˢ B.markBand k)) := (sum_restrict_bands_eq B μ hμ.1).symm
    _ = Measure.sum (fun k => ν.restrict (univ ×ˢ B.markBand k)) := congrArg Measure.sum (funext hband)
    _ = ν := sum_restrict_bands_eq B ν hν.1

end ProphetSecretary.Limiting.CountableInstance
