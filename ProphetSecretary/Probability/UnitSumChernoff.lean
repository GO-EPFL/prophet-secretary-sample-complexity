import ProphetSecretary.Analysis.ClassifierExponential
import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Integral.Pi

/-!
# Explicit Poisson-form Chernoff bounds for independent unit offers

The exponential chord proves the moment-generating bound from actual independent
product coordinates. The constants retain the source classifier's exponents;
there is no assumed Bernstein concentration interface.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Probability

variable {ι : Type*} [Fintype ι]

lemma unit_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x∈Icc (0:ℝ) 1) : Integrable id μ :=
  Integrable.of_bound measurable_id.aestronglyMeasurable 1 (hμ.mono fun x hx => by
    change |x|≤1
    rw [abs_of_nonneg hx.1]
    exact hx.2)

lemma unit_exp_integrable (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x∈Icc (0:ℝ) 1) (t : ℝ) : Integrable (fun x => Real.exp (t*x)) μ := by
  apply Integrable.of_bound ((measurable_id.const_mul t).exp.aestronglyMeasurable) (Real.exp |t|)
  filter_upwards [hμ] with x hx
  rw [Real.norm_eq_abs,abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  calc
    t*x≤|t*x| := le_abs_self _
    _=|t| *|x| := abs_mul _ _
    _≤|t| := mul_le_of_le_one_right (abs_nonneg _) (by rw [abs_of_nonneg hx.1];exact hx.2)

lemma unit_exp_integral_le (μ : Measure ℝ) [IsProbabilityMeasure μ]
    (hμ : ∀ᵐ x ∂μ, x∈Icc (0:ℝ) 1) (t : ℝ) :
    (∫ x, Real.exp (t*x) ∂μ)≤Real.exp ((Real.exp t-1)*(∫ x, x ∂μ)) := by
  have hX : Integrable (fun x : ℝ => x) μ := unit_integrable μ hμ
  have hChordI : Integrable (fun x => 1+x*(Real.exp t-1)) μ := (integrable_const 1).add (hX.mul_const _)
  calc
    (∫ x, Real.exp (t*x) ∂μ)≤∫ x, 1+x*(Real.exp t-1) ∂μ :=
      integral_mono_ae (unit_exp_integrable μ hμ t) hChordI
        (hμ.mono fun x hx => ProphetSecretary.Analysis.exp_mul_unit_chord t x hx)
    _=1+(Real.exp t-1)*(∫ x, x ∂μ) := by
      rw [integral_add (integrable_const 1) (hX.mul_const _),integral_const,probReal_univ,one_smul,integral_mul_const,mul_comm]
    _≤Real.exp ((Real.exp t-1)*(∫ x, x ∂μ)) := by
      simpa only [add_comm] using Real.add_one_le_exp ((Real.exp t-1)*(∫ x, x ∂μ))

noncomputable def coordinateSum (a : ι → ℝ) : ℝ := ∑ i, a i

lemma coordinateSum_exp_integrable (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x∈Icc (0:ℝ) 1) (t : ℝ) :
    Integrable (fun a => Real.exp (t*coordinateSum a)) (Measure.pi μ) := by
  have hInd : iIndepFun (fun i (a : ι → ℝ) => a i) (Measure.pi μ) :=
    iIndepFun_pi (fun _ => measurable_id.aemeasurable)
  have hEach (i : ι) : Integrable (fun a : ι → ℝ => Real.exp (t*a i)) (Measure.pi μ) :=
    (measurePreserving_eval μ i).integrable_comp_of_integrable (unit_exp_integrable (μ i) (hμ i) t)
  simpa only [coordinateSum,Finset.sum_apply] using
    hInd.integrable_exp_mul_sum (fun _ => measurable_pi_apply _) (fun i _ => hEach i) (t:=t) (s:=Finset.univ)

lemma coordinateSum_mgf_le (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x∈Icc (0:ℝ) 1) (t : ℝ) :
    mgf coordinateSum (Measure.pi μ) t≤Real.exp ((Real.exp t-1)*(∑ i, ∫ x, x ∂μ i)) := by
  change (∫ a : ι → ℝ, Real.exp (t*∑ i, a i) ∂Measure.pi μ)≤_
  have hExpr : (fun a : ι → ℝ => Real.exp (t*∑ i, a i))=fun a => ∏ i, Real.exp (t*a i) := by
    funext a
    rw [Finset.mul_sum,Real.exp_sum]
  rw [hExpr,integral_fintype_prod_eq_prod (fun _ (x : ℝ) => Real.exp (t*x))]
  calc
    (∏ i, ∫ x, Real.exp (t*x) ∂μ i)≤∏ i, Real.exp ((Real.exp t-1)*(∫ x, x ∂μ i)) :=
      Finset.prod_le_prod (fun _ _ => integral_nonneg fun _ => (Real.exp_pos _).le)
        (fun i _ => unit_exp_integral_le (μ i) (hμ i) t)
    _=Real.exp ((Real.exp t-1)*(∑ i, ∫ x, x ∂μ i)) := by
      rw [←Real.exp_sum,Finset.mul_sum]

/-- Unit-coordinate upper tail with the source exponent 3/8. -/
theorem coordinateSum_upper_classifier_tail (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x∈Icc (0:ℝ) 1) {T : ℝ} (hT : 0≤T)
    (hMean : (∑ i, ∫ x, x ∂μ i)≤T) :
    (Measure.pi μ).real {a | 2*T≤coordinateSum a}≤Real.exp (-3*T/8) := by
  have h := measure_ge_le_exp_mul_mgf (X:=coordinateSum) (μ:=Measure.pi μ) (t:=(2/3:ℝ))
    (2*T) (by norm_num) (coordinateSum_exp_integrable μ hμ (2/3))
  have hM := coordinateSum_mgf_le μ hμ (2/3)
  have hc0 : 0≤Real.exp (2/3:ℝ)-1 := by
    have h1 := Real.one_le_exp_iff.mpr (show (0:ℝ)≤2/3 by norm_num)
    linarith only [h1]
  have hcT := mul_le_mul_of_nonneg_left hMean hc0
  have hc := mul_le_mul_of_nonneg_right (ProphetSecretary.Analysis.exp_two_thirds_le) hT
  calc
    (Measure.pi μ).real {a | 2*T≤coordinateSum a}≤Real.exp (-(2/3:ℝ)*(2*T))*
        Real.exp ((Real.exp (2/3:ℝ)-1)*(∑ i, ∫ x, x ∂μ i)) :=
      h.trans (mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le)
    _≤Real.exp (-3*T/8) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [hcT,hc]

/-- Unit-coordinate lower tail with the source exponent 1/6. -/
theorem coordinateSum_lower_classifier_tail (μ : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (μ i)]
    (hμ : ∀ i, ∀ᵐ x ∂μ i, x∈Icc (0:ℝ) 1) {T : ℝ} (hT : 0≤T)
    (hMean : 3*T≤∑ i, ∫ x, x ∂μ i) :
    (Measure.pi μ).real {a | coordinateSum a≤2*T}≤Real.exp (-T/6) := by
  have h := measure_le_le_exp_mul_mgf (X:=coordinateSum) (μ:=Measure.pi μ) (t:=(-1/3:ℝ))
    (2*T) (by norm_num) (coordinateSum_exp_integrable μ hμ (-1/3))
  have hM := coordinateSum_mgf_le μ hμ (-1/3)
  have hc0 : Real.exp (-1/3:ℝ)-1≤0 := by linarith [ProphetSecretary.Analysis.exp_neg_third_le]
  have hcT := mul_le_mul_of_nonpos_left hMean hc0
  have hc := mul_le_mul_of_nonneg_right (ProphetSecretary.Analysis.exp_neg_third_le)
    (mul_nonneg (by norm_num : (0:ℝ)≤3) hT)
  calc
    (Measure.pi μ).real {a | coordinateSum a≤2*T}≤Real.exp (-(-1/3:ℝ)*(2*T))*
        Real.exp ((Real.exp (-1/3:ℝ)-1)*(∑ i, ∫ x, x ∂μ i)) :=
      h.trans (mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le)
    _≤Real.exp (-T/6) := by
      rw [←Real.exp_add]
      apply Real.exp_le_exp.mpr
      nlinarith only [hcT,hc]

end ProphetSecretary.Probability
