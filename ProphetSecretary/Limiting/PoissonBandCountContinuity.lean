import ProphetSecretary.Limiting.PoissonCounts
import Mathlib.Topology.Algebra.Order.Field

/-!
# Continuity of a positive-band count on each finite array

A count is locally constant when no mark lies on the chosen band boundary.
The total count provides a deterministic bound, including an empty array.
-/
open MeasureTheory Set Filter
open scoped Topology Classical BigOperators
namespace ProphetSecretary.Limiting

lemma pointCount_le_count (S : Set Point) (ω : Configuration) : pointCount S ω≤ω.1 := by
  unfold pointCount
  calc
    _ ≤ ∑ _j : Fin ω.1, (1:ℕ) := Finset.sum_le_sum (fun j _ => by split_ifs <;> omega)
    _ = _ := by simp

lemma upperBandBit_continuousAt {b x : ℝ} (h : x≠b) :
    ContinuousAt (fun y : ℝ => if b<y then (1:ℝ) else 0) x := by
  by_cases hx : b<x
  · have he : (fun y : ℝ => if b<y then (1:ℝ) else 0) =ᶠ[𝓝 x] fun _ => 1 := by
      filter_upwards [Ioi_mem_nhds hx] with y hy
      exact if_pos hy
    exact (continuousAt_congr he).mpr continuousAt_const
  · have hx' : x<b := lt_of_le_of_ne (not_lt.mp hx) h
    have he : (fun y : ℝ => if b<y then (1:ℝ) else 0) =ᶠ[𝓝 x] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hx'] with y hy
      exact if_neg (not_lt_of_ge hy.le)
    exact (continuousAt_congr he).mpr continuousAt_const

lemma pointCount_upperBand_branch_continuousAt {N : ℕ} (b : ℝ) (v : Fin N → Point)
    (hv : ∀ j, (v j).2≠b) :
    ContinuousAt (fun q : Fin N → Point => (pointCount (univ ×ˢ Ioi b) (configurationMk N q):ℝ)) v := by
  have hRep : (fun q : Fin N → Point => (pointCount (univ ×ˢ Ioi b) (configurationMk N q):ℝ)) =
      (fun q => ∑ j, if b<(q j).2 then (1:ℝ) else 0) := by
    funext q
    simp only [pointCount,configurationMk,mem_prod,mem_univ,true_and,mem_Ioi,Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> norm_num
  rw [hRep]
  apply tendsto_finsetSum Finset.univ
  intro j _
  exact (upperBandBit_continuousAt (hv j)).comp' (f := fun q : Fin N → Point => (q j).2)
    (continuous_snd.comp (continuous_apply j)).continuousAt
end ProphetSecretary.Limiting
