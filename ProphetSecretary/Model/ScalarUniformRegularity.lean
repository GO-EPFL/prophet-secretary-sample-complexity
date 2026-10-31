import ProphetSecretary.Model.ScalarHessian
import Mathlib.MeasureTheory.Integral.IntervalIntegral.AbsolutelyContinuousFun

/-!
# Uniform local scalar C^{1,1}

The preliminary finite-cardinality Lipschitz derivative supplies absolute
continuity. Integrating the sharp almost-everywhere Hessian bound then removes
all dependence on cardinality or the offer laws.
-/

open MeasureTheory Set
open scoped Topology NNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.scalarUnit_deriv_increment_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a b lam rho : ℝ}
    (ha : 0 < a) (hb : b < 1) (hlam : lam ∈ Icc a b) (hrho : rho ∈ Icc a b) (horder : lam ≤ rho) :
    deriv (fun z ↦ optimalScalarValue P z (1 - z)) rho -
      deriv (fun z ↦ optimalScalarValue P z (1 - z)) lam ≤
        (1 / (a ^ 2 * (1 - b))) * (rho - lam) := by
  let f : ℝ → ℝ := fun z ↦ optimalScalarValue P z (1 - z)
  let g := deriv f
  obtain ⟨L, _hL, hLip⟩ := (P.scalarState_finite_C11 hP (u := 1) ⟨zero_le_one, le_rfl⟩).2 a b ha hb
  simp only [mul_one] at hLip
  have hAC : AbsolutelyContinuousOnInterval g lam rho := by
    apply LipschitzOnWith.absolutelyContinuousOnInterval (K := L)
    rw [uIcc_of_le horder]
    exact hLip.mono (Icc_subset_Icc hlam.1 hrho.2)
  have hinside : Icc lam rho ⊆ Ioo (0 : ℝ) 1 := fun t ht ↦
    ⟨ha.trans_le (hlam.1.trans ht.1), (ht.2.trans hrho.2).trans_lt hb⟩
  have hbound : ∀ᵐ t ∂volume.restrict (Icc lam rho), deriv g t ≤ 1 / (a ^ 2 * (1 - b)) := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hinside (P.scalarCurvature_ae hP),
      ae_restrict_mem measurableSet_Icc] with t ht hmem
    have hta : a ≤ t := hlam.1.trans hmem.1
    have htb : t ≤ b := hmem.2.trans hrho.2
    have hsmall : 0 < a ^ 2 * (1 - b) := mul_pos (sq_pos_of_pos ha) (sub_pos.mpr hb)
    have hsq : a ^ 2 ≤ t ^ 2 := by nlinarith
    have hden : a ^ 2 * (1 - b) ≤ t ^ 2 * (1 - t) :=
      mul_le_mul hsq (by linarith) (sub_pos.mpr hb).le (sq_nonneg t)
    exact ht.2.trans (one_div_le_one_div_of_le hsmall hden)
  have hI := intervalIntegral.integral_mono_ae_restrict horder hAC.intervalIntegrable_deriv
    intervalIntegrable_const hbound
  rw [hAC.integral_deriv_eq_sub, intervalIntegral.integral_const, smul_eq_mul] at hI
  simpa only [mul_comm] using hI

/-- Explicit uniform derivative Lipschitz bound on every interior interval. -/
theorem Instance.scalarUnit_deriv_lipschitz_uniform (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {a b lam rho : ℝ}
    (ha : 0 < a) (hb : b < 1) (hlam : lam ∈ Icc a b) (hrho : rho ∈ Icc a b) :
    |deriv (fun z ↦ optimalScalarValue P z (1 - z)) rho -
      deriv (fun z ↦ optimalScalarValue P z (1 - z)) lam| ≤
        (1 / (a ^ 2 * (1 - b))) * |rho - lam| := by
  have hconv : ConvexOn ℝ (Ioo (0 : ℝ) 1) (fun z ↦ optimalScalarValue P z (1 - z)) :=
    (optimalScalarValue_weight_convex P hP).subset Ioo_subset_Icc_self (convex_Ioo _ _)
  have hmono := hconv.monotoneOn_deriv (fun z hz ↦ (P.scalarUnit_hasDerivAt hP hz).differentiableAt)
  have hmono' : MonotoneOn (deriv (fun z ↦ optimalScalarValue P z (1 - z))) (Icc a b) :=
    hmono.mono (fun z hz ↦ ⟨ha.trans_le hz.1, hz.2.trans_lt hb⟩)
  rcases le_total lam rho with horder | horder
  · rw [abs_of_nonneg (sub_nonneg.mpr (hmono' hlam hrho horder)), abs_of_nonneg (sub_nonneg.mpr horder)]
    exact P.scalarUnit_deriv_increment_le hP ha hb hlam hrho horder
  · rw [abs_sub_comm, abs_sub_comm rho lam,
      abs_of_nonneg (sub_nonneg.mpr (hmono' hrho hlam horder)), abs_of_nonneg (sub_nonneg.mpr horder)]
    exact P.scalarUnit_deriv_increment_le hP ha hb hrho hlam horder

/-- Uniform local C^{1,1} data with an explicit constant depending only on the
interior scalar interval. -/
theorem Instance.scalarUnit_uniform_C11 (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) :
    (∀ lam ∈ Ioo (0 : ℝ) 1, DifferentiableAt ℝ (fun z ↦ optimalScalarValue P z (1 - z)) lam) ∧
      ∀ (a b : ℝ) (_ha : 0 < a) (hb : b < 1),
        LipschitzOnWith (NNReal.mk (1 / (a ^ 2 * (1 - b)))
          (div_nonneg zero_le_one (mul_nonneg (sq_nonneg a) (sub_pos.mpr hb).le)))
          (deriv (fun z ↦ optimalScalarValue P z (1 - z))) (Icc a b) := by
  refine ⟨fun lam hlam ↦ (P.scalarUnit_hasDerivAt hP hlam).differentiableAt, ?_⟩
  intro a b ha hb
  rw [lipschitzOnWith_iff_dist_le_mul]
  intro lam hlam rho hrho
  simpa only [Real.dist_eq, NNReal.coe_mk] using P.scalarUnit_deriv_lipschitz_uniform hP ha hb hrho hlam

end ProphetSecretary.Model
