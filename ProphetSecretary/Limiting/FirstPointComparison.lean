import ProphetSecretary.Limiting.RawFirstPointReward

/-!
# Comparing first points after deleting accepted offers

Measure order compares the measurable time functional even without an attained
first atom. Identification of a preserved selection below uses an explicit
singleton first slice. Total accepted mass after that point may be infinite.
-/

open MeasureTheory Set Filter
open scoped Classical ENNReal

namespace ProphetSecretary.Limiting.FirstPoint

lemma time_antitone {μ ν : Measure Point} (hνμ : ν ≤ μ) : time μ ≤ time ν := by
  have hBound : BddBelow (range (cumulativeTime μ)) :=
    ⟨0,fun _ ⟨q,hq⟩ => hq ▸ (cumulativeTime_bounds μ q).1⟩
  apply ciInf_mono hBound
  intro q
  by_cases hν : 0 < ν (Iio (q : ℝ) ×ˢ univ)
  · have hμ : 0 < μ (Iio (q : ℝ) ×ˢ univ) := hν.trans_le
      (Measure.le_iff.mp hνμ _ (measurableSet_Iio.prod MeasurableSet.univ))
    simp only [cumulativeTime,if_pos hμ,if_pos hν,le_refl]
  · have he : cumulativeTime ν q = 1 := by rw [cumulativeTime,if_neg hν]
    rw [he]
    exact (cumulativeTime_bounds μ q).2

lemma rational_cumulative_zero_before_time (μ : Measure Point)
    (hNonneg : ∀ᵐ p ∂μ, 0 ≤ p.1) {q : ℚ} (hq : (q : ℝ) < time μ) :
    μ (Iio (q : ℝ) ×ˢ univ) = 0 := by
  by_cases hq0 : (q : ℝ) ≤ 0
  · have hz : μ (Iio (0 : ℝ) ×ˢ univ) = 0 := measure_eq_zero_iff_ae_notMem.mpr
      (hNonneg.mono (fun p hp hmem => (not_lt_of_ge hp) hmem.1))
    have hsub : (Iio (q : ℝ) ×ˢ univ : Set Point) ⊆ Iio (0 : ℝ) ×ˢ univ :=
      fun _ hp => ⟨hp.1.trans_le hq0,hp.2⟩
    exact measure_mono_null hsub hz
  · by_contra hne
    have hp : 0 < μ (Iio (q : ℝ) ×ˢ univ) := pos_iff_ne_zero.mpr hne
    have hc : cumulativeTime μ q = (q : ℝ) := by
      rw [cumulativeTime,if_pos hp,min_eq_right (hq.trans_le (time_bounds μ).2).le,
        max_eq_right (lt_of_not_ge hq0).le]
    have hBound : BddBelow (range (cumulativeTime μ)) :=
      ⟨0,fun _ ⟨r,hr⟩ => hr ▸ (cumulativeTime_bounds μ r).1⟩
    have ht : time μ ≤ (q : ℝ) := (ciInf_le hBound q).trans_eq hc
    exact (not_lt_of_ge ht) hq

/-- Nonnegative clock support rules out mass before the measured first time,
without a finite-total-mass assumption. -/
lemma measure_before_time_eq_zero (μ : Measure Point) (hNonneg : ∀ᵐ p ∂μ, 0 ≤ p.1) :
    μ (Iio (time μ) ×ˢ univ) = 0 := by
  let Q := {q : ℚ // (q : ℝ) < time μ}
  have hUnion : (⋃ q : Q, (Iio (q.1 : ℝ) ×ˢ univ)) = (Iio (time μ) ×ˢ univ : Set Point) := by
    ext p
    constructor
    · intro hp
      obtain ⟨q,hq⟩ := mem_iUnion.mp hp
      exact ⟨hq.1.trans q.2,hq.2⟩
    · intro hp
      obtain ⟨q,hpq,hqt⟩ := exists_rat_btwn (show p.1 < time μ from hp.1)
      exact mem_iUnion.mpr ⟨⟨q,hqt⟩,⟨hpq,hp.2⟩⟩
  rw [← hUnion]
  exact measure_iUnion_null (fun q => rational_cumulative_zero_before_time μ hNonneg q.2)

lemma time_eq_of_first_atom (ν : Measure Point) {t x : ℝ} (ht : t ∈ Icc (0 : ℝ) 1)
    (hPast : ν (Iio t ×ˢ univ) = 0) (hAtom : 0 < ν {(t,x)}) : time ν = t := by
  apply time_eq_of_rational_cumulatives ν ht
  · intro q hq
    by_contra hn
    have hqt : (q : ℝ) < t := lt_of_not_ge hn
    have hsub : (Iio (q : ℝ) ×ˢ univ : Set Point) ⊆ Iio t ×ˢ univ :=
      fun _ hp => ⟨hp.1.trans hqt,hp.2⟩
    have hz : ν (Iio (q : ℝ) ×ˢ univ) = 0 := measure_mono_null hsub hPast
    rw [hz] at hq
    exact (lt_irrefl 0) hq
  · intro q hq
    exact hAtom.trans_le (measure_mono (singleton_subset_iff.mpr ⟨hq,mem_univ x⟩))

lemma slice_preserved_of_high_restriction {μ ν : Measure Point} {t x d : ℝ}
    (hνμ : ν ≤ μ) (hHigh : ν.restrict {p : Point | d < p.2} = μ.restrict {p : Point | d < p.2})
    (hx : d < x) (hSlice : μ.restrict {p : Point | p.1 = t} = Measure.dirac (t,x)) :
    ν.restrict {p : Point | p.1 = t} = Measure.dirac (t,x) := by
  let S := {p : Point | p.1 = t}
  let H := {p : Point | d < p.2}
  have hS : MeasurableSet S := measurableSet_eq_fun measurable_fst measurable_const
  have hH : MeasurableSet H := measurableSet_lt measurable_const measurable_snd
  have hComm (ρ : Measure Point) : (ρ.restrict S).restrict H = (ρ.restrict H).restrict S := by
    rw [Measure.restrict_restrict hH,Measure.restrict_restrict hS,inter_comm]
  have hRetained : (ν.restrict S).restrict H = Measure.dirac (t,x) := by
    rw [hComm ν,hHigh,← hComm μ,hSlice,restrict_dirac,if_pos (show (t,x) ∈ H from hx)]
  have hUpper : ν.restrict S ≤ Measure.dirac (t,x) :=
    (Measure.restrict_mono_measure hνμ S).trans_eq hSlice
  apply le_antisymm hUpper
  calc
    _ = (ν.restrict S).restrict H := hRetained.symm
    _ ≤ ν.restrict S := Measure.restrict_le_self

lemma measure_atom_positive_of_slice {μ : Measure Point} {t x : ℝ}
    (hSlice : μ.restrict {p : Point | p.1 = t} = Measure.dirac (t,x)) : 0 < μ {(t,x)} := by
  have hDom : Measure.dirac (t,x) ≤ μ := by rw [← hSlice]; exact Measure.restrict_le_self
  exact (by simp : (0 : ℝ≥0∞) < Measure.dirac (t,x) {(t,x)}).trans_le
    (Measure.le_iff.mp hDom _ (measurableSet_singleton _))

theorem first_point_preserved_of_high_restriction {μ ν : Measure Point} {x d : ℝ}
    (hNonneg : ∀ᵐ p ∂μ, 0 ≤ p.1) (hνμ : ν ≤ μ)
    (hHigh : ν.restrict {p : Point | d < p.2} = μ.restrict {p : Point | d < p.2})
    (hx : d < x) (hSlice : μ.restrict {p : Point | p.1 = time μ} = Measure.dirac (time μ,x)) :
    time ν = time μ ∧ ν.restrict {p : Point | p.1 = time ν} = Measure.dirac (time ν,x) := by
  have hNewSlice := slice_preserved_of_high_restriction hνμ hHigh hx hSlice
  have hPast : ν (Iio (time μ) ×ˢ univ) = 0 := by
    have hle := Measure.le_iff.mp hνμ (Iio (time μ) ×ˢ univ) (measurableSet_Iio.prod MeasurableSet.univ)
    rw [measure_before_time_eq_zero μ hNonneg] at hle
    exact le_antisymm hle zero_le
  have ht := time_eq_of_first_atom ν (time_bounds μ) hPast (measure_atom_positive_of_slice hNewSlice)
  exact ⟨ht,by simpa only [ht] using hNewSlice⟩

theorem rawReward_preserved_of_high_restriction (a : ℝ) {μ ν : Measure Point} {x d : ℝ}
    (hNonneg : ∀ᵐ p ∂μ, 0 ≤ p.1) (hνμ : ν ≤ μ)
    (hHigh : ν.restrict {p : Point | d < p.2} = μ.restrict {p : Point | d < p.2})
    (hx : d < x) (hx0 : 0 ≤ x)
    (hSlice : μ.restrict {p : Point | p.1 = time μ} = Measure.dirac (time μ,x)) :
    rawReward a ν = rawReward a μ := by
  have hNew := (first_point_preserved_of_high_restriction hNonneg hνμ hHigh hx hSlice).2
  have hμPos : 0 < μ univ := (measure_atom_positive_of_slice hSlice).trans_le (measure_mono (subset_univ _))
  have hνPos : 0 < ν univ := (measure_atom_positive_of_slice hNew).trans_le (measure_mono (subset_univ _))
  rw [rawReward_of_firstSlice a ν hx0 hνPos.ne' hNew,rawReward_of_firstSlice a μ hx0 hμPos.ne' hSlice]

end ProphetSecretary.Limiting.FirstPoint
