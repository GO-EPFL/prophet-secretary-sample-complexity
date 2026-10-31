import Mathlib.Topology.Instances.Rat
import Mathlib.Data.Rat.Encodable
import Mathlib.Topology.Order.IsLUB

/-!
# A countable dense enumeration of elapsed observation times

All enumerated times lie in [0,1), every rational in that interval occurs, and
approximations from below recover a bound at any positive elapsed time through
one-sided limits. The enumeration adds no random observation.
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Probability

noncomputable def rationalObservationTime (j : ℕ) : ℝ :=
  match Encodable.decode (α := ℚ) j with
  | none => 0
  | some q => if (0 : ℝ) ≤ q ∧ (q : ℝ) < 1 then q else 0

lemma rationalObservationTime_mem (j : ℕ) : rationalObservationTime j ∈ Ico (0 : ℝ) 1 := by
  unfold rationalObservationTime
  cases Encodable.decode (α := ℚ) j with
  | none => exact ⟨le_rfl, zero_lt_one⟩
  | some q =>
    simp only
    split_ifs with h
    · exact h
    · exact ⟨le_rfl, zero_lt_one⟩

lemma rationalObservationTime_covers (q : ℚ) (hq : (q : ℝ) ∈ Ico (0 : ℝ) 1) :
    rationalObservationTime (Encodable.encode q) = q := by
  simp only [rationalObservationTime, Encodable.encodek]
  exact if_pos hq

lemma mem_closure_rationalObservationTime_left {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) :
    t ∈ closure (range rationalObservationTime ∩ Iio t) := by
  apply Metric.mem_closure_iff.mpr
  intro ε hε
  have hb : max 0 (t-ε) < t := max_lt_iff.mpr ⟨ht0, by linarith⟩
  obtain ⟨q, hqlo, hqhi⟩ := exists_rat_btwn hb
  have hq0 : (0 : ℝ) ≤ q := (le_max_left _ _).trans hqlo.le
  have hq1 : (q : ℝ) < 1 := hqhi.trans_le ht1
  have heq := rationalObservationTime_covers q ⟨hq0,hq1⟩
  refine ⟨q, ⟨⟨Encodable.encode q, heq⟩, hqhi⟩, ?_⟩
  rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hqhi.le)]
  have h := (le_max_right (0 : ℝ) (t-ε)).trans_lt hqlo
  linarith only [h]

/-- A bound on the enumerated observations extends through any left limit. -/
theorem le_of_rationalObservationTime_left_limit {f : ℝ → ℝ} {t B : ℝ}
    (ht0 : 0 < t) (ht1 : t ≤ 1) (hf : Tendsto f (𝓝[<] t) (𝓝 (f t)))
    (hB : ∀ j, f (rationalObservationTime j) ≤ B) : f t ≤ B := by
  let S := range rationalObservationTime ∩ Iio t
  letI : (𝓝[S] t).NeBot := mem_closure_iff_nhdsWithin_neBot.mp (mem_closure_rationalObservationTime_left ht0 ht1)
  have hlim := hf.mono_left (nhdsWithin_mono t (show S ⊆ Iio t from inter_subset_right))
  apply le_of_tendsto hlim
  filter_upwards [self_mem_nhdsWithin (a := t) (s := S)] with s hs
  obtain ⟨j, rfl⟩ := hs.1
  exact hB j

end ProphetSecretary.Probability
