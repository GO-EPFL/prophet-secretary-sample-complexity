import ProphetSecretary.Probability.LocalMGF
import Mathlib.Probability.Moments.Variance

/-!
# A lower-tail bound with the actual variance

Independent centered bounded summands have a local Gaussian Laplace bound.
The choice of the Laplace parameter below retains small total variance;
no factor depending on the number of summands enters the bound.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal

namespace ProphetSecretary.Probability

variable {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : ι → Ω → ℝ}

lemma mgf_sum_le_exp_variance (hInd : iIndepFun X μ)
    (hX : ∀ i, Measurable (X i)) (b : ℝ≥0)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hMean : ∀ i, (∫ ω, X i ω ∂μ) = 0) {t : ℝ} (ht : |t| * b ≤ 1) :
    mgf (fun ω => ∑ i, X i ω) μ t ≤
      Real.exp (t^2*variance (fun ω => ∑ i, X i ω) μ) := by
  classical
  have hSum : (fun ω => ∑ i, X i ω) = ∑ i, X i := by
    funext ω
    simp
  have hLp (i : ι) : MemLp (X i) 2 μ :=
    MemLp.of_bound (hX i).aestronglyMeasurable b (by simpa only [Real.norm_eq_abs] using hb i)
  have hSmall (i : ι) : ∀ᵐ ω ∂μ, |t*X i ω| ≤ 1 := by
    filter_upwards [hb i] with ω hω
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hω (abs_nonneg t)).trans ht
  have hEach (i : ι) : mgf (X i) μ t ≤ Real.exp (t^2*(∫ ω, X i ω^2 ∂μ)) :=
    mgf_le_exp_secondMoment_of_small (hX i) ((hLp i).integrable (by norm_num))
      (hLp i).integrable_sq (hMean i) (hSmall i)
  have hVar : variance (fun ω => ∑ i, X i ω) μ = ∑ i, ∫ ω, X i ω^2 ∂μ := by
    have h := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hLp i)
      (fun i _ j _ hij => hInd.indepFun hij)
    rw [hSum,h]
    apply Finset.sum_congr rfl
    intro i _
    rw [variance_eq_integral (hX i).aemeasurable,hMean i]
    simp
  calc
    mgf (fun ω => ∑ i, X i ω) μ t = ∏ i, mgf (X i) μ t := by
      rw [hSum]
      exact hInd.mgf_sum hX Finset.univ
    _ ≤ ∏ i, Real.exp (t^2*(∫ ω, X i ω^2 ∂μ)) :=
      Finset.prod_le_prod (fun _ _ => mgf_nonneg) (fun i _ => hEach i)
    _ = Real.exp (t^2*variance (fun ω => ∑ i, X i ω) μ) := by
      rw [hVar,Finset.mul_sum,Real.exp_sum]

/-- A convenient Bernstein-regime bound. The positive variance proxy may be
larger than the actual variance; `r*b ≤ 2*v` keeps the optimizing Laplace
parameter inside the local range. -/
theorem measure_sum_le_neg (hInd : iIndepFun X μ)
    (hX : ∀ i, Measurable (X i)) (b : ℝ≥0)
    (hb : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hMean : ∀ i, (∫ ω, X i ω ∂μ) = 0)
    {r v : ℝ} (hr : 0 < r) (hv : 0 < v)
    (hVar : variance (fun ω => ∑ i, X i ω) μ ≤ v) (hRange : r*b ≤ 2*v) :
    μ.real {ω | (∑ i, X i ω) ≤ -r} ≤ Real.exp (-(r^2/(4*v))) := by
  let t : ℝ := -r/(2*v)
  have ht : t ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith only [hr]) (by positivity)
  have hSmall : |t| * b ≤ 1 := by
    rw [abs_of_nonpos ht]
    change -(-r/(2*v))*(b : ℝ) ≤ 1
    rw [neg_div,neg_neg,div_mul_eq_mul_div]
    exact (div_le_one (by positivity)).mpr hRange
  have hInt (i : ι) : Integrable (fun ω => Real.exp (t*X i ω)) μ := by
    apply integrable_exp_mul_of_small (hX i)
    filter_upwards [hb i] with ω hω
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_left hω (abs_nonneg t)).trans hSmall
  have hExp : Integrable (fun ω => Real.exp (t*(∑ i, X i ω))) μ := by
    simpa only [Finset.sum_apply] using hInd.integrable_exp_mul_sum hX (s := Finset.univ) (fun i _ => hInt i)
  have hM := mgf_sum_le_exp_variance hInd hX b hb hMean hSmall
  calc
    μ.real {ω | (∑ i, X i ω) ≤ -r} ≤ Real.exp (-t*(-r))*mgf (fun ω => ∑ i, X i ω) μ t :=
      measure_le_le_exp_mul_mgf (-r) ht hExp
    _ ≤ Real.exp (-t*(-r))*Real.exp (t^2*variance (fun ω => ∑ i, X i ω) μ) :=
      mul_le_mul_of_nonneg_left hM (Real.exp_pos _).le
    _ = Real.exp (-t*(-r)+t^2*variance (fun ω => ∑ i, X i ω) μ) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (-t*(-r)+t^2*v) := Real.exp_le_exp.mpr
      (add_le_add le_rfl (mul_le_mul_of_nonneg_left hVar (sq_nonneg t)))
    _ = Real.exp (-(r^2/(4*v))) := by
      congr 1
      dsimp only [t]
      field_simp
      ring

end ProphetSecretary.Probability
