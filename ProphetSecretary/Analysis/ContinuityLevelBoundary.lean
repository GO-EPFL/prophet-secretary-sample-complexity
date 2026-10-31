import Mathlib.Topology.Order.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Continuous

/-!
# Null boundaries for threshold events of almost continuous payoffs

At a point where a real-valued function is continuous, a level-event boundary
can occur only at that level. This local form is needed for the continuity-set
step of score-weighted configuration limits; global payoff continuity is not
assumed.
-/

open Set Filter
open scoped Topology

namespace ProphetSecretary.Analysis

variable {Ω : Type*} [TopologicalSpace Ω]

lemma levelBoundary_eq_of_continuousAt {f : Ω → ℝ} {x : Ω} {a : ℝ}
    (hc : ContinuousAt f x) (hx : x ∈ frontier {y | a ≤ f y}) : f x = a := by
  by_contra hn
  rcases lt_or_gt_of_ne hn with hlt | hgt
  · have hev : ∀ᶠ y in 𝓝 x, f y < a := hc.eventually (Iio_mem_nhds hlt)
    have hcomp : {y | a ≤ f y}ᶜ ∈ 𝓝 x := by
      filter_upwards [hev] with y hy
      exact not_le.mpr hy
    obtain ⟨y, hyN, hyS⟩ := (mem_closure_iff_nhds.mp hx.1) _ hcomp
    exact hyN hyS
  · have hev : ∀ᶠ y in 𝓝 x, a < f y := hc.eventually (Ioi_mem_nhds hgt)
    have hmem : {y | a ≤ f y} ∈ 𝓝 x := by
      filter_upwards [hev] with y hy
      exact hy.le
    exact hx.2 (mem_interior_iff_mem_nhds.mpr hmem)

end ProphetSecretary.Analysis
