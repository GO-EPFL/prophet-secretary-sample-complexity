import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Algebra.Order.Group.MinMax
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.Tactic

/-!
# Differentiating a bounded displacement inside a maximum

Only ties at occurrences with nonzero displacement must be excluded. A
uniform Lipschitz bound justifies differentiating the expectation.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace ProphetSecretary.Probability

lemma hasDerivAt_displaced_max (x y a : ℝ) (hRegular : a=0 ∨ x≠y) :
    HasDerivAt (fun θ : ℝ => max (x+θ*a) y) (if y<x then a else 0) 0 := by
  by_cases ha : a=0
  · subst a
    simpa only [mul_zero,add_zero,ite_self] using hasDerivAt_const (0 : ℝ) (max x y)
  have hxy : x≠y := hRegular.resolve_left ha
  by_cases hyx : y<x
  · rw [if_pos hyx]
    have hd : HasDerivAt (fun θ : ℝ => x+θ*a) a 0 := by
      simpa only [one_mul,id_eq] using ((hasDerivAt_id (0 : ℝ)).mul_const a).const_add x
    apply hd.congr_of_eventuallyEq
    filter_upwards [hd.continuousAt.eventually (lt_mem_nhds (show y<x+0*a by simpa only [zero_mul,add_zero] using hyx))] with θ hθ
    exact max_eq_left hθ.le
  · rw [if_neg hyx]
    have hxylt : x<y := lt_of_le_of_ne (not_lt.mp hyx) hxy
    have hc : ContinuousAt (fun θ : ℝ => x+θ*a) 0 := by fun_prop
    apply (hasDerivAt_const (0 : ℝ) y).congr_of_eventuallyEq
    filter_upwards [hc.eventually (gt_mem_nhds (show x+0*a<y by simpa only [zero_mul,add_zero] using hxylt))] with θ hθ
    exact max_eq_right hθ.le

lemma hasDerivAt_expected_displaced_max {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsFiniteMeasure μ] (X Y A : Ω → ℝ)
    (hX : Measurable X) (hY : Measurable Y) (hA : Measurable A)
    (hXI : Integrable X μ) (hYI : Integrable Y μ) {D : ℝ} (hD : 0≤D)
    (hBound : ∀ᵐ ω ∂μ, |A ω|≤D) (hRegular : ∀ᵐ ω ∂μ, A ω=0 ∨ X ω≠Y ω) :
    HasDerivAt (fun θ : ℝ => ∫ ω, max (X ω+θ*A ω) (Y ω) ∂μ)
      (∫ ω, if Y ω<X ω then A ω else 0 ∂μ) 0 := by
  have hMeas (θ : ℝ) : Measurable (fun ω => max (X ω+θ*A ω) (Y ω)) := (hX.add (hA.const_mul θ)).max hY
  have hDerivMeas : Measurable (fun ω => if Y ω<X ω then A ω else 0) :=
    Measurable.ite (measurableSet_lt hY hX) hA measurable_const
  have hInt : Integrable (fun ω => max (X ω+0*A ω) (Y ω)) μ := by
    apply (hXI.norm.add hYI.norm).mono' (hMeas 0).aestronglyMeasurable
    exact Eventually.of_forall (fun ω => by
      simp only [Pi.add_apply,Real.norm_eq_abs,zero_mul,add_zero]
      by_cases hxy : X ω≤Y ω
      · rw [max_eq_right hxy]
        exact le_add_of_nonneg_left (abs_nonneg _)
      · rw [max_eq_left (not_le.mp hxy).le]
        exact le_add_of_nonneg_right (abs_nonneg _))
  have hLip : ∀ᵐ ω ∂μ, LipschitzOnWith (Real.nnabs D) (fun θ : ℝ => max (X ω+θ*A ω) (Y ω)) univ := by
    filter_upwards [hBound] with ω hω
    apply LipschitzWith.lipschitzOnWith
    apply LipschitzWith.of_dist_le_mul
    intro θ η
    simp only [Real.dist_eq,Real.coe_nnabs,abs_of_nonneg hD]
    calc
      _ ≤ |(X ω+θ*A ω)-(X ω+η*A ω)| := abs_max_sub_max_le_abs _ _ _
      _ = |θ-η| * |A ω| := by rw [show (X ω+θ*A ω)-(X ω+η*A ω)=(θ-η)*A ω by ring,abs_mul]
      _ ≤ |θ-η| * D := mul_le_mul_of_nonneg_left hω (abs_nonneg _)
      _ = _ := mul_comm _ _
  exact (hasDerivAt_integral_of_dominated_loc_of_lip (s := univ) (F := fun θ ω => max (X ω+θ*A ω) (Y ω))
    (F' := fun ω => if Y ω<X ω then A ω else 0) (bound := fun _ => D) (μ := μ)
    (by simp only [univ_mem]) (Eventually.of_forall (fun θ => (hMeas θ).aestronglyMeasurable)) hInt
    hDerivMeas.aestronglyMeasurable hLip (integrable_const D)
    (hRegular.mono (fun ω hω => hasDerivAt_displaced_max (X ω) (Y ω) (A ω) hω))).2

end ProphetSecretary.Probability
