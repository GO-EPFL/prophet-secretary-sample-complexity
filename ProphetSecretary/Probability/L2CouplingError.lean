import ProphetSecretary.Probability.BoundedCouplingError
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Square-integrable observables on a small exceptional event

The expectation error is bounded by the square root of the event probability
times the sum of second moments. Complete-vector score observables need not
be bounded for this analytical coupling estimate.
-/
open MeasureTheory Set Filter
open scoped ENNReal
namespace ProphetSecretary.Probability
variable {Ω : Type*} [MeasurableSpace Ω]

lemma integral_sub_abs_le_of_eq_off_L2 (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Ω → ℝ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    {If Ig : ℝ} (hIf : (∫ q, (f q)^2 ∂μ)≤If) (hIg : (∫ q, (g q)^2 ∂μ)≤Ig)
    (E : Set Ω) (hE : MeasurableSet E) (hEq : ∀ q, q∉E → f q=g q) :
    |(∫ q, f q ∂μ)-(∫ q, g q ∂μ)| ≤ Real.sqrt (2*(If+Ig)*μ.real E) := by
  let Y : Ω → ℝ := E.indicator (fun _ => 1)
  have hYLp : MemLp Y 2 μ := (memLp_const (1:ℝ)).indicator hE
  have hYL0 (q : Ω) : 0≤Y q := by unfold Y; by_cases hq : q∈E <;> simp [hq]
  have hL : MemLp (fun q => f q-g q) 2 μ := hf.sub hg
  have hf2 := (memLp_two_iff_integrable_sq hf.aestronglyMeasurable).mp hf
  have hg2 := (memLp_two_iff_integrable_sq hg.aestronglyMeasurable).mp hg
  have hL2 := (memLp_two_iff_integrable_sq hL.aestronglyMeasurable).mp hL
  have hMoment : (∫ q, (f q-g q)^2 ∂μ)≤2*(If+Ig) := by
    calc
      _ ≤ ∫ q, 2*(f q)^2+2*(g q)^2 ∂μ := by
        apply integral_mono hL2 ((hf2.const_mul 2).add (hg2.const_mul 2))
        intro q
        change (f q-g q)^2≤2*(f q)^2+2*(g q)^2
        nlinarith [sq_nonneg (f q+g q)]
      _ = 2*(∫ q, (f q)^2 ∂μ)+2*(∫ q, (g q)^2 ∂μ) := by
        rw [integral_add (hf2.const_mul 2) (hg2.const_mul 2),integral_const_mul,integral_const_mul]
      _ ≤ _ := by linarith
  have hMoment0 : 0≤2*(If+Ig) := (integral_nonneg (fun q => sq_nonneg (f q-g q))).trans hMoment
  have hYsq : (∫ q, (Y q)^2 ∂μ)=μ.real E := by
    have heq : (fun q => (Y q)^2)=E.indicator (fun _ => (1:ℝ)) := by
      funext q
      unfold Y
      by_cases hq : q∈E <;> simp [hq]
    rw [heq,integral_indicator_const _ hE,smul_eq_mul,mul_one]
  have hHolder := integral_mul_norm_le_Lp_mul_Lq (μ := μ) Real.HolderConjugate.two_two
    (show MemLp (fun q => f q-g q) (ENNReal.ofReal (2:ℝ)) μ by simpa using hL)
    (show MemLp Y (ENNReal.ofReal (2:ℝ)) μ by simpa using hYLp)
  have hCS : (∫ q, |f q-g q| * Y q ∂μ)≤
      Real.sqrt (∫ q, (f q-g q)^2 ∂μ)*Real.sqrt (μ.real E) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (hYL0 _),Real.rpow_two,sq_abs,← Real.sqrt_eq_rpow,hYsq] using hHolder
  rw [← integral_sub (hf.integrable (by norm_num)) (hg.integrable (by norm_num))]
  calc
    _ ≤ ∫ q, |f q-g q| ∂μ := abs_integral_le_integral_abs
    _ = ∫ q, |f q-g q| * Y q ∂μ := by
      apply integral_congr_ae
      exact Eventually.of_forall (fun q => by
        by_cases hq : q∈E
        · simp [Y,hq]
        · simp [Y,hq,hEq q hq])
    _ ≤ Real.sqrt (∫ q, (f q-g q)^2 ∂μ)*Real.sqrt (μ.real E) := hCS
    _ ≤ Real.sqrt (2*(If+Ig))*Real.sqrt (μ.real E) :=
      mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hMoment) (Real.sqrt_nonneg _)
    _ = _ := (Real.sqrt_mul hMoment0 _).symm
end ProphetSecretary.Probability
