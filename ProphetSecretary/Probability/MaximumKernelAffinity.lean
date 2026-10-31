import ProphetSecretary.Probability.ConstantCdfSupportGap
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Affinity of an expected maximum and mean contraction

With no competing-law mass between two endpoints, the expected maximum is
affine throughout their closed interval. Endpoint atoms are permitted. A
strict competing CDF constant on almost every marginal value supplies the
required gap, so replacing that marginal by its mean preserves the expected
maximum. The CDF premise concerns all marginal values, including zero atoms.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal
namespace ProphetSecretary.Probability

theorem integral_max_affine_of_gap (ν : Measure ℝ) [IsFiniteMeasure ν]
    (hY : Integrable id ν) {a b x : ℝ} (hGap : ν (Ioo a b)=0) (hx : x ∈ Icc a b) :
    (∫ y, max x y ∂ν)=(∫ y, max a y ∂ν)+ν.real (Iic a)*(x-a) := by
  let I : ℝ → ℝ := fun y => if y≤a then 1 else 0
  have hI : Integrable I ν := by
    apply Integrable.of_bound (Measurable.ite measurableSet_Iic measurable_const measurable_const).aestronglyMeasurable 1
    exact Eventually.of_forall (fun y => by split_ifs <;> norm_num)
  have hIa : (∫ y, I y ∂ν)=ν.real (Iic a) := by
    simpa only [I,Set.indicator_apply,Set.mem_Iic,Pi.one_apply] using (integral_indicator_one (μ := ν) measurableSet_Iic)
  have hMaxA : Integrable (fun y => max a y) ν := (integrable_const a).sup hY
  have hNoGap := measure_eq_zero_iff_ae_notMem.mp hGap
  have hPoint : (fun y => max x y)=ᵐ[ν] fun y => max a y+I y*(x-a) := by
    filter_upwards [hNoGap] with y hy
    by_cases hya : y≤a
    · rw [max_eq_left (hya.trans hx.1),max_eq_left hya]
      simp only [I,if_pos hya,one_mul]
      ring
    · have hby : b≤y := le_of_not_gt (fun hyb => hy ⟨lt_of_not_ge hya,hyb⟩)
      rw [max_eq_right (hx.2.trans hby),max_eq_right (le_of_not_ge hya)]
      simp only [I,if_neg hya,zero_mul,add_zero]
  rw [integral_congr_ae hPoint,integral_add hMaxA (hI.mul_const (x-a)),integral_mul_const,hIa]

theorem expected_maximum_mean_contraction_of_constant_strictCdf
    (κ ν : Measure ℝ) [IsProbabilityMeasure κ] [IsFiniteMeasure ν] (H : ℝ≥0)
    (hSupp : ∀ᵐ x ∂κ, x ∈ Icc (0 : ℝ) H) (hY : Integrable id ν)
    (k : ℝ) (hCdf : ∀ᵐ x ∂κ, ν.real (Iio x)=k) :
    Integrable (fun x => ∫ y, max x y ∂ν) κ ∧
      (∫ x, (∫ y, max x y ∂ν) ∂κ)=∫ y, max (∫ x, x ∂κ) y ∂ν := by
  obtain ⟨a,b,ha,hb,hGap⟩ := strictCdf_ae_constant_support_gap κ ν H hSupp k hCdf
  have hX : Integrable id κ := by
    apply Integrable.of_bound measurable_id.aestronglyMeasurable (H : ℝ)
    filter_upwards [hSupp] with x hx
    change ‖x‖ ≤ (H : ℝ)
    rw [Real.norm_eq_abs,abs_of_nonneg hx.1]
    exact hx.2
  let p : ℝ := ν.real (Iic a)
  let G : ℝ → ℝ := fun x => ∫ y, max x y ∂ν
  have hAffine : G =ᵐ[κ] fun x => G a+p*(x-a) := by
    have hSupport : ∀ᵐ x ∂κ, x ∈ κ.support := κ.support_mem_ae
    filter_upwards [hSupport] with x hx
    exact integral_max_affine_of_gap ν hY hGap ⟨ha.2 hx,hb.2 hx⟩
  have hAffineInt : Integrable (fun x => G a+p*(x-a)) κ := by
    exact (integrable_const (G a)).add ((hX.sub (integrable_const a)).const_mul p)
  refine ⟨hAffineInt.congr hAffine.symm,?_⟩
  have hMean := mean_mem_Icc_of_support_extrema κ hX ha hb
  have hLinear : Integrable (fun x : ℝ => p*(x-a)) κ := (hX.sub (integrable_const a)).const_mul p
  have hDifference : (∫ x : ℝ, x-a ∂κ)=(∫ x, x ∂κ)-a := by
    simpa only [integral_const,probReal_univ,one_smul] using
      (integral_sub (f := fun x : ℝ => x) (g := fun _ => a) hX (integrable_const a))
  calc
    _ = ∫ x, G a+p*(x-a) ∂κ := integral_congr_ae hAffine
    _ = G a+p*((∫ x, x ∂κ)-a) := by
      rw [integral_add (f := fun _ => G a) (g := fun x => p*(x-a)) (integrable_const (G a)) hLinear,
        integral_const_mul,hDifference]
      simp only [integral_const,probReal_univ,one_smul]
    _ = _ := (integral_max_affine_of_gap ν hY hGap hMean).symm

end ProphetSecretary.Probability
