import ProphetSecretary.Probability.AntitoneKernelConstancy

/-!
# A constant competing CDF leaves no mass inside the supported hull

If a strict CDF is constant almost everywhere for a bounded marginal, its
measure has no mass strictly between that marginal's support extrema. Null
support endpoints need not themselves satisfy the CDF equality. Positive
neighborhood mass supplies good marginal values on either side of every
interior point, avoiding any endpoint continuity assumption on the CDF.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Probability

theorem strictCdf_ae_constant_support_gap (κ ν : Measure ℝ)
    [IsProbabilityMeasure κ] [IsFiniteMeasure ν] (H : ℝ≥0)
    (hSupp : ∀ᵐ x ∂κ, x ∈ Icc (0 : ℝ) H)
    (k : ℝ) (hCdf : ∀ᵐ x ∂κ, ν.real (Iio x)=k) :
    ∃ a b : ℝ, IsLeast κ.support a ∧ IsGreatest κ.support b ∧ ν (Ioo a b)=0 := by
  obtain ⟨a,b,ha,hb⟩ := bounded_probability_support_extrema κ H hSupp
  have hDisjoint (y : ℝ) (hy : y ∈ Ioo a b) : y ∉ ν.support := by
    have hLeft : 0 < κ (Iio y) := (κ.mem_support_iff_forall a).mp ha.1 _ (Iio_mem_nhds hy.1)
    have hRight : 0 < κ (Ioi y) := (κ.mem_support_iff_forall b).mp hb.1 _ (Ioi_mem_nhds hy.2)
    obtain ⟨l,hl,hFl⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (ne_of_gt hLeft) (ae_restrict_of_ae hCdf)
    obtain ⟨r,hr,hFr⟩ := Measure.exists_mem_of_measure_ne_zero_of_ae (ne_of_gt hRight) (ae_restrict_of_ae hCdf)
    have hLR : l < r := hl.trans hr
    have hMass : ν (Iio l)=ν (Iio r) :=
      (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp (hFl.trans hFr.symm)
    have hGap : ν (Ioo l r)=0 := by
      have hDiff : ν (Iio r \ Iio l)=0 := by
        rw [measure_sdiff (Iio_subset_Iio hLR.le) measurableSet_Iio.nullMeasurableSet (measure_ne_top _ _),hMass,tsub_self]
      apply measure_mono_null _ hDiff
      intro z hz
      exact ⟨hz.2,not_lt.mpr hz.1.le⟩
    intro hySupport
    have hPos := (ν.mem_support_iff_forall y).mp hySupport (Ioo l r) (Ioo_mem_nhds hl hr)
    rw [hGap] at hPos
    exact (lt_irrefl (0 : ℝ≥0∞)) hPos
  refine ⟨a,b,ha,hb,?_⟩
  apply measure_eq_zero_iff_ae_notMem.mpr
  have hSupport : ∀ᵐ y ∂ν, y ∈ ν.support := ν.support_mem_ae
  exact hSupport.mono (fun y hy hI => hDisjoint y hI hy)

end ProphetSecretary.Probability
