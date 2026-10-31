import Mathlib.Analysis.Calculus.Monotone
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Almost-everywhere differentiability of a Lipschitz real slope

Adding its Lipschitz constant times the coordinate makes the slope monotone.
The real monotone differentiation theorem then applies, and subtracting the
linear function gives the desired derivative.
-/

open MeasureTheory Set
open scoped Topology NNReal

namespace ProphetSecretary.Analysis

lemma lipschitzOn_ae_differentiableAt {g : ℝ → ℝ} {a b : ℝ} {K : ℝ≥0}
    (hLip : LipschitzOnWith K g (Ioo a b)) :
    ∀ᵐ x ∂volume.restrict (Ioo a b), DifferentiableAt ℝ g x := by
  have hMono : MonotoneOn (fun x ↦ g x + (K : ℝ) * x) (Ioo a b) := by
    rw [lipschitzOnWith_iff_dist_le_mul] at hLip
    intro x hx y hy hxy
    have h := hLip x hx y hy
    simp only [Real.dist_eq] at h
    rw [abs_sub_comm x y, abs_of_nonneg (sub_nonneg.mpr hxy)] at h
    linarith [le_abs_self (g x - g y)]
  filter_upwards [hMono.ae_differentiableWithinAt measurableSet_Ioo,
    ae_restrict_mem measurableSet_Ioo] with x hx hmem
  have hD := hx.differentiableAt (Ioo_mem_nhds hmem.1 hmem.2)
  have hLin := (hasDerivAt_mul_const (x := x) (K : ℝ)).differentiableAt
  have hSub := hD.sub hLin
  have he : (fun y ↦ (g y + (K : ℝ) * y) - y * (K : ℝ)) = g := by
    funext y
    ring
  change DifferentiableAt ℝ (fun y ↦ (g y + (K : ℝ) * y) - y * (K : ℝ)) x at hSub
  rw [he] at hSub
  exact hSub

end ProphetSecretary.Analysis
