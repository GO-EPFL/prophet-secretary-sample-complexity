import ProphetSecretary.Limiting.FiniteIntensityPoisson
import Mathlib.Data.Rat.Denumerable

/-!
# The first accepted time from an observable point measure

Rational cumulative evaluations give a globally measurable time functional.
Its identification with an executed first point uses explicit attainment
conditions, never just an infimum of an arbitrary accepted set.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.FirstPoint

noncomputable def cumulativeTime (μ : Measure Point) (q : ℚ) : ℝ :=
  if 0 < μ (Iio (q : ℝ) ×ˢ univ) then max 0 (min 1 (q : ℝ)) else 1

noncomputable def time (μ : Measure Point) : ℝ := ⨅ q : ℚ, cumulativeTime μ q

lemma cumulativeTime_bounds (μ : Measure Point) (q : ℚ) : cumulativeTime μ q ∈ Icc (0 : ℝ) 1 := by
  unfold cumulativeTime
  split_ifs
  · exact ⟨le_max_left _ _,max_le zero_le_one (min_le_left _ _)⟩
  · exact ⟨zero_le_one,le_rfl⟩

lemma time_bounds (μ : Measure Point) : time μ ∈ Icc (0 : ℝ) 1 := by
  have hbound : BddBelow (Set.range (cumulativeTime μ)) :=
    ⟨0,fun _ ⟨q,hq⟩ => hq ▸ (cumulativeTime_bounds μ q).1⟩
  exact ⟨le_ciInf (fun q => (cumulativeTime_bounds μ q).1),
    (ciInf_le hbound (0 : ℚ)).trans (cumulativeTime_bounds μ 0).2⟩

lemma measurable_time : Measurable time := by
  apply Measurable.iInf
  intro q
  exact Measurable.ite (measurableSet_lt measurable_const
    (Measure.measurable_coe (measurableSet_Iio.prod MeasurableSet.univ))) measurable_const measurable_const

lemma time_eq_of_rational_cumulatives (μ : Measure Point) {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1)
    (hbelow : ∀ q : ℚ, 0 < μ (Iio (q : ℝ) ×ˢ univ) → s ≤ (q : ℝ))
    (habove : ∀ q : ℚ, s < (q : ℝ) → 0 < μ (Iio (q : ℝ) ×ˢ univ)) : time μ = s := by
  apply le_antisymm
  · by_contra hn
    have hst : s < time μ := lt_of_not_ge hn
    have hs1 : s < 1 := hst.trans_le (time_bounds μ).2
    obtain ⟨q,hsq,hqt⟩ := exists_rat_btwn (lt_min hs1 hst)
    have hqpos : 0 ≤ (q : ℝ) := hs.1.trans hsq.le
    have hq1 : (q : ℝ) ≤ 1 := (lt_min_iff.mp hqt).1.le
    have hc : cumulativeTime μ q = (q : ℝ) := by
      rw [cumulativeTime,if_pos (habove q hsq),min_eq_right hq1,max_eq_right hqpos]
    have hbound : BddBelow (Set.range (cumulativeTime μ)) :=
      ⟨0,fun _ ⟨q,hq⟩ => hq ▸ (cumulativeTime_bounds μ q).1⟩
    have hle : time μ ≤ (q : ℝ) := (ciInf_le hbound q).trans_eq hc
    exact (not_lt_of_ge hle) (lt_min_iff.mp hqt).2
  · apply le_ciInf
    intro q
    unfold cumulativeTime
    split_ifs with hq
    · exact le_max_of_le_right (le_min hs.2 (hbelow q hq))
    · exact hs.2

lemma time_eq_one_of_empty_cumulatives (μ : Measure Point)
    (hzero : ∀ q : ℚ, μ (Iio (q : ℝ) ×ˢ univ) = 0) : time μ = 1 := by
  have he : cumulativeTime μ = fun _ => 1 := by
    funext q
    simp [cumulativeTime,hzero q]
  rw [time,he,ciInf_const]

end ProphetSecretary.Limiting.FirstPoint
