import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace

/-!
# Integrating the pilot tail envelope

A Cauchy kernel dominates the capped inverse-square tail. Its integral gives
an explicit uniform constant, avoiding any dependence on the number of offers.
The integral is over the whole positive half-line, which also bounds (0,1].
-/

open MeasureTheory Set

namespace ProphetSecretary.Analysis

lemma min_one_inv_sq_le_cauchy (x : ℝ) :
    min 1 (1/x^2) ≤ 2/(1+x^2) := by
  by_cases hx0 : x = 0
  · subst x; norm_num
  have hx2 : 0 < x^2 := sq_pos_of_ne_zero hx0
  have hd : 0 < 1+x^2 := by positivity
  by_cases hx1 : x^2 ≤ 1
  · exact (min_le_left _ _).trans ((le_div_iff₀ hd).mpr (by linarith))
  · exact (min_le_right _ _).trans ((div_le_div_iff₀ hx2 hd).mpr (by linarith))

lemma capped_inverse_square_integrable_and_integral {B : ℝ} (hB : 0 < B) :
    Integrable (fun s : ℝ => min 1 (B^2/s^2)) ∧
      (∫ s in Ioi (0 : ℝ), min 1 (B^2/s^2)) ≤ 2*B*Real.pi := by
  let f := fun s : ℝ => min 1 (B^2/s^2)
  let g := fun s : ℝ => 2*(1+(B⁻¹*s)^2)⁻¹
  have hfi : Measurable f := measurable_const.min (measurable_const.div (measurable_id.pow_const 2))
  have hf0 (s : ℝ) : 0 ≤ f s := le_min zero_le_one (by positivity)
  have hg0 (s : ℝ) : 0 ≤ g s := by dsimp only [g]; positivity
  have hgi : Integrable g :=
    (integrable_inv_one_add_sq.comp_mul_left' (inv_ne_zero hB.ne')).const_mul 2
  have hfg (s : ℝ) : f s ≤ g s := by
    have heq : B^2/s^2 = 1/(B⁻¹*s)^2 := by
      by_cases hs : s = 0
      · subst s; simp
      · field_simp
    change min 1 (B^2/s^2) ≤ 2*(1+(B⁻¹*s)^2)⁻¹
    rw [heq]
    simpa only [div_eq_mul_inv] using min_one_inv_sq_le_cauchy (B⁻¹*s)
  have hInt : Integrable f := hgi.mono' hfi.aestronglyMeasurable
    (Filter.Eventually.of_forall fun s => by simpa only [Real.norm_eq_abs,abs_of_nonneg (hf0 s)] using hfg s)
  have hIntegral : (∫ s, g s) = 2*B*Real.pi := by
    rw [show g = fun s : ℝ => 2*(1+(B⁻¹*s)^2)⁻¹ from rfl,integral_const_mul,
      Measure.integral_comp_mul_left (fun t : ℝ => (1+t^2)⁻¹),integral_univ_inv_one_add_sq]
    simp only [inv_inv,abs_of_pos hB,smul_eq_mul]
    ring
  refine ⟨hInt,?_⟩
  calc
    (∫ s in Ioi (0 : ℝ), f s) ≤ ∫ s in Ioi (0 : ℝ), g s :=
      integral_mono hInt.integrableOn hgi.integrableOn hfg
    _ ≤ ∫ s, g s := setIntegral_le_integral hgi (Filter.Eventually.of_forall hg0)
    _ = _ := hIntegral

/-- Explicit integrability and an O(A+B) bound before any asymptotic notation. -/
theorem pilot_tail_envelope_integral {A B : ℝ} (hA : 0 < A) (hB : 0 < B) :
    IntegrableOn (fun s : ℝ => Real.exp (-s/A)+min 1 (B^2/s^2)) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), (Real.exp (-s/A)+min 1 (B^2/s^2))) ≤ A+2*B*Real.pi := by
  have hNeg : -A⁻¹ < 0 := neg_neg_of_pos (inv_pos.mpr hA)
  have hExp : IntegrableOn (fun s : ℝ => Real.exp (-s/A)) (Ioi 0) := by
    simpa only [div_eq_mul_inv,neg_mul,mul_neg,mul_comm] using integrableOn_exp_mul_Ioi hNeg 0
  have hExpInt : (∫ s in Ioi (0 : ℝ), Real.exp (-s/A)) = A := by
    have h := integral_exp_mul_Ioi hNeg 0
    simp only [mul_zero,Real.exp_zero,neg_div_neg_eq,one_div,inv_inv] at h
    simpa only [div_eq_mul_inv,neg_mul,mul_neg,mul_comm] using h
  obtain ⟨hPoly,hPolyInt⟩ := capped_inverse_square_integrable_and_integral hB
  refine ⟨hExp.add hPoly.integrableOn,?_⟩
  rw [integral_add hExp hPoly.integrableOn,hExpInt]
  exact add_le_add le_rfl hPolyInt

/-- The literal envelope in `eq:bayes-fixed-tail`. The variance coefficient v
may subsequently be instantiated by 64*Kδ*(1+S), independently of n. -/
theorem fixed_weight_tail_integral {v m : ℝ} (hv : 0 < v) (hm : 0 < m) :
    IntegrableOn (fun s : ℝ => Real.exp (-(m*s/v))+min 1 (16/(m^2*s^2))) (Ioi 0) ∧
    (∫ s in Ioi (0 : ℝ), (Real.exp (-(m*s/v))+min 1 (16/(m^2*s^2)))) ≤
      (v+8*Real.pi)/m := by
  have h := pilot_tail_envelope_integral (div_pos hv hm) (div_pos (by norm_num : (0 : ℝ) < 4) hm)
  have heq : (fun s : ℝ => Real.exp (-(m*s/v))+min 1 (16/(m^2*s^2))) =
      (fun s => Real.exp (-s/(v/m))+min 1 ((4/m)^2/s^2)) := by
    funext s
    have hExp : -(m*s/v) = -s/(v/m) := by field_simp
    have hPoly : (4/m)^2/s^2 = 16/(m^2*s^2) := by
      rw [div_pow,div_div]
      norm_num
    rw [hExp,hPoly]
  rw [heq]
  refine ⟨h.1,h.2.trans_eq ?_⟩
  ring

end ProphetSecretary.Analysis
