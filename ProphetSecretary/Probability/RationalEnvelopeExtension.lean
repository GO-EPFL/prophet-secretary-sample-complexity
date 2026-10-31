import ProphetSecretary.Probability.RationalObservationTimes

/-!
# Extending an enumerated envelope through one-sided limits

A single countable family of inequalities controls every unit-interval
parameter when the underlying function has left limits equal to its values.
Positive affine time changes preserve the one-sided observation order.
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Probability

theorem unitInterval_bound_of_leftLimits {f : ℝ → ℝ} {B : ℝ}
    (hlim : ∀ t ∈ Ioc (0 : ℝ) 1, Tendsto f (𝓝[<] t) (𝓝 (f t)))
    (hgrid : ∀ j, f (rationalObservationTime j) ≤ B) : ∀ t ∈ Icc (0 : ℝ) 1, f t ≤ B := by
  intro t ht
  by_cases hzero : t=0
  · have heq := rationalObservationTime_covers (0 : ℚ) (by norm_num : ((0 : ℚ) : ℝ) ∈ Ico (0 : ℝ) 1)
    have h := hgrid (Encodable.encode (0 : ℚ))
    simpa only [heq,Rat.cast_zero,hzero] using h
  · have ht0 : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm hzero)
    exact le_of_rationalObservationTime_left_limit ht0 ht.2 (hlim t ⟨ht0,ht.2⟩) hgrid

lemma tendsto_positive_affine_left (a b t : ℝ) (hb : 0 < b) :
    Tendsto (fun s : ℝ => a+b*s) (𝓝[<] t) (𝓝[<] (a+b*t)) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · exact (continuous_const.add (continuous_const.mul continuous_id)).continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin (a := t) (s := Iio t)] with s hs
    have h := mul_lt_mul_of_pos_left hs hb
    change a+b*s < a+b*t
    linarith only [h]

end ProphetSecretary.Probability
