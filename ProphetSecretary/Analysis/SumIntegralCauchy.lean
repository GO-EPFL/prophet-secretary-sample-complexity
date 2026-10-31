import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Algebra.QuadraticDiscriminant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Cauchy-Schwarz across marginal integrals

The direct-sum integral inequality follows by integrating a nonnegative square
and applying the quadratic discriminant test. No finite-support coordinates or
choice of an orthonormal basis is needed.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Analysis

lemma sum_integral_mul_sq_le {ι Ω : Type*} [Fintype ι] [MeasurableSpace Ω]
    (μ : ι → Measure Ω) (f g : ι → Ω → ℝ)
    (hf : ∀ i, MemLp (f i) 2 (μ i)) (hg : ∀ i, MemLp (g i) 2 (μ i)) :
    (∑ i, ∫ x, f i x * g i x ∂μ i) ^ 2 ≤
      (∑ i, ∫ x, f i x ^ 2 ∂μ i) * (∑ i, ∫ x, g i x ^ 2 ∂μ i) := by
  have hcross (i : ι) : Integrable (fun x ↦ f i x * g i x) (μ i) := (hf i).integrable_mul (hg i)
  have hpoly (i : ι) (t : ℝ) : (∫ x, (t * f i x + g i x) ^ 2 ∂μ i) =
      t ^ 2 * (∫ x, f i x ^ 2 ∂μ i) + (2 * t) * (∫ x, f i x * g i x ∂μ i) + (∫ x, g i x ^ 2 ∂μ i) := by
    have he : (fun x ↦ (t * f i x + g i x) ^ 2) =
        (fun x ↦ t ^ 2 * f i x ^ 2 + (2 * t) * (f i x * g i x) + g i x ^ 2) := by
      funext x
      ring
    rw [he, integral_add (f := fun x ↦ t ^ 2 * f i x ^ 2 + (2 * t) * (f i x * g i x))
        (g := fun x ↦ g i x ^ 2)
        (((hf i).integrable_sq.const_mul (t ^ 2)).add ((hcross i).const_mul (2 * t))) (hg i).integrable_sq,
      integral_add (f := fun x ↦ t ^ 2 * f i x ^ 2) (g := fun x ↦ (2 * t) * (f i x * g i x))
        ((hf i).integrable_sq.const_mul (t ^ 2)) ((hcross i).const_mul (2 * t)), integral_const_mul, integral_const_mul]
  have hD : discrim (∑ i, ∫ x, f i x ^ 2 ∂μ i)
      (2 * ∑ i, ∫ x, f i x * g i x ∂μ i) (∑ i, ∫ x, g i x ^ 2 ∂μ i) ≤ 0 := by
    apply discrim_le_zero
    intro t
    have h : 0 ≤ ∑ i : ι, ∫ x, (t * f i x + g i x) ^ 2 ∂μ i :=
      Finset.sum_nonneg (fun i _ ↦ integral_nonneg (μ := μ i) (fun x ↦ sq_nonneg (t * f i x + g i x)))
    simp_rw [hpoly] at h
    simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at h
    convert h using 1 <;> first | rfl | ring
  unfold discrim at hD
  nlinarith

end ProphetSecretary.Analysis
