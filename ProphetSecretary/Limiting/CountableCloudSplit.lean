import ProphetSecretary.Limiting.CountableHighLowIndependence

/-!
# Independent cloud splitting on the actual countable probability space

All actual marks lie above the reserve. The high and low restrictions therefore
reconstruct the full anonymous counting measure almost surely. Their proved
independence identifies its law with the sum of independently sampled pieces.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

lemma bandCountingMeasure_below_reserve_zero_ae :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, bandCountingMeasure ω (univ ×ˢ Iic (B.terminal : ℝ)) = 0 := by
  let S : Set Point := univ ×ˢ Iic (B.terminal : ℝ)
  have hS : MeasurableSet S := MeasurableSet.univ.prod measurableSet_Iic
  filter_upwards [B.bandConfigurations_marks_in_band] with ω hω
  have hzero (k : ℕ) : countingMeasure (ω k) S = 0 := by
    rw [countingMeasure_eq_pointCount hS]
    have hn : pointCount S (ω k) = 0 := by
      unfold pointCount
      apply Finset.sum_eq_zero
      intro j _
      have hm : (B.terminal : ℝ) < ((ω k).2 j).2 :=
        (B.terminal_lt_markCutoff k).trans (B.markBand_subset_tail k (hω k j))
      have hp : (ω k).2 j ∉ S := fun hp => (not_le_of_gt hm) hp.2
      exact if_neg hp
    rw [hn,Nat.cast_zero]
  change bandCountingMeasure ω S = 0
  rw [bandCountingMeasure,Measure.sum_apply _ hS]
  simp only [hzero,tsum_zero]

lemma bandCountingMeasure_restrict_above_reserve_ae :
    ∀ᵐ ω ∂B.bandConfigurationsLaw,
      (bandCountingMeasure ω).restrict (univ ×ˢ Ioi (B.terminal : ℝ)) = bandCountingMeasure ω := by
  filter_upwards [B.bandCountingMeasure_below_reserve_zero_ae] with ω hω
  apply Measure.restrict_eq_self_of_ae_mem
  filter_upwards [measure_eq_zero_iff_ae_notMem.mp hω] with p hp
  have hm : (B.terminal : ℝ) < p.2 := by
    simpa only [mem_prod,mem_univ,true_and,mem_Iic,not_le] using hp
  exact ⟨mem_univ _,hm⟩

lemma bandCountingMeasure_high_low_split_ae {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    ∀ᵐ ω ∂B.bandConfigurationsLaw, bandCountingMeasure ω =
      (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b) +
        (bandCountingMeasure ω).restrict (univ ×ˢ Ioc (B.terminal : ℝ) b) := by
  let U : Set Point := univ ×ˢ Ioi b
  let V : Set Point := univ ×ˢ Ioc (B.terminal : ℝ) b
  have hV : MeasurableSet V := MeasurableSet.univ.prod measurableSet_Ioc
  have hUV : Disjoint U V := Set.disjoint_left.mpr (fun p hpU hpV => (not_lt_of_ge hpV.2.2) hpU.2)
  have hUnion : U ∪ V = (univ ×ˢ Ioi (B.terminal : ℝ) : Set Point) := by
    ext p
    simp only [U,V,mem_union,mem_prod,mem_univ,true_and,mem_Ioi,mem_Ioc]
    constructor
    · rintro (h | h)
      · exact hb.trans h
      · exact h.1
    · intro hp
      rcases lt_or_ge b p.2 with h | h
      · exact Or.inl h
      · exact Or.inr ⟨hp,h⟩
  filter_upwards [B.bandCountingMeasure_restrict_above_reserve_ae] with ω hω
  change bandCountingMeasure ω = (bandCountingMeasure ω).restrict U + (bandCountingMeasure ω).restrict V
  rw [← Measure.restrict_union hUV hV,hUnion,hω]

/-- The entire cloud can be generated as the sum of independent high and
omitted-low random measures, including an infinite-intensity low cloud. -/
theorem bandCountingMeasure_high_low_law {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    B.bandConfigurationsLaw.map bandCountingMeasure =
      ((B.bandConfigurationsLaw.map (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b))).prod
        (B.bandConfigurationsLaw.map (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioc (B.terminal : ℝ) b)))).map
          (fun p : Measure Point × Measure Point => p.1+p.2) := by
  let H := fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioi b)
  let L := fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioc (B.terminal : ℝ) b)
  have hH : Measurable H :=
    (measurable_restrict_pointMeasure (MeasurableSet.univ.prod measurableSet_Ioi)).comp measurable_bandCountingMeasure
  have hL : Measurable L :=
    (measurable_restrict_pointMeasure (MeasurableSet.univ.prod measurableSet_Ioc)).comp measurable_bandCountingMeasure
  have hJoint := (B.high_low_positive_independent hb).map_prod_eq_prod_map_map hH.aemeasurable hL.aemeasurable
  calc
    _ = B.bandConfigurationsLaw.map (fun ω => H ω+L ω) :=
      Measure.map_congr (B.bandCountingMeasure_high_low_split_ae hb)
    _ = (B.bandConfigurationsLaw.map (fun ω => (H ω,L ω))).map
        (fun p : Measure Point × Measure Point => p.1+p.2) :=
      (Measure.map_map (measurable_fst.add measurable_snd) (hH.prodMk hL)).symm
    _ = _ := congrArg (fun μ : Measure (Measure Point × Measure Point) => μ.map
      (fun p : Measure Point × Measure Point => p.1+p.2)) hJoint

/-- The retained high component may equivalently be sampled from the actual
finite-intensity Poisson configuration; the low component is independent. -/
theorem bandCountingMeasure_poisson_low_law {b : ℝ} (hb : (B.terminal : ℝ) < b) :
    B.bandConfigurationsLaw.map bandCountingMeasure =
      (((configurationLaw (B.intensityAbove b hb)).map countingMeasure).prod
        (B.bandConfigurationsLaw.map (fun ω => (bandCountingMeasure ω).restrict (univ ×ˢ Ioc (B.terminal : ℝ) b)))).map
          (fun p : Measure Point × Measure Point => p.1+p.2) := by
  rw [B.bandCountingMeasure_high_low_law hb,B.cutoff_countingMeasure_law hb]

end ProphetSecretary.Limiting.CountableInstance
