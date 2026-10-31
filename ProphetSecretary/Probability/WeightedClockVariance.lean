import ProphetSecretary.Probability.FourthMoment
import ProphetSecretary.Reach.ReachIntegralBounds
import Mathlib.Probability.Moments.Variance

/-!
# Weighted independent clock fluctuations

Independent event indicators have an exact weighted variance. The absolute
mean bound is uniform in the number of coordinates and depends on the sum
of squared weights, as needed for the causal Poisson approximation.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Probability

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] {N : ℕ}

lemma weighted_centeredIndicator_secondMoment {A : Set Ω} (hA : MeasurableSet A) (a : Fin N → ℝ) :
    (∫ u : Fin N → Ω, (∑ i, a i * centeredIndicator A (μ.real A) (u i)) ^ 2
      ∂Measure.pi (fun _ : Fin N => μ)) =
      μ.real A * (1 - μ.real A) * ∑ i, (a i) ^ 2 := by
  let X : Fin N → Ω → ℝ := fun i ω => a i * centeredIndicator A (μ.real A) ω
  let Y : (Fin N → Ω) → ℝ := fun u => ∑ i, X i (u i)
  have hXm (i : Fin N) : Measurable (X i) := (centeredIndicator_measurable hA _).const_mul _
  have hXb (i : Fin N) (ω : Ω) : |X i ω| ≤ |a i| := by
    simpa only [X, abs_mul, mul_one] using mul_le_mul_of_nonneg_left
      (centeredIndicator_abs_le_one A measureReal_nonneg measureReal_le_one ω) (abs_nonneg (a i))
  have hXLp (i : Fin N) : MemLp (X i) 2 μ :=
    MemLp.of_bound (hXm i).aestronglyMeasurable |a i|
      (Filter.Eventually.of_forall (fun ω => by simpa only [Real.norm_eq_abs] using hXb i ω))
  have hXI (i : Fin N) : Integrable (X i) μ := (hXLp i).integrable (by norm_num)
  have hXmean (i : Fin N) : (∫ ω, X i ω ∂μ) = 0 := by
    rw [show X i = (fun ω => a i * centeredIndicator A (μ.real A) ω) from rfl,
      integral_const_mul, centeredIndicator_mean hA, mul_zero]
  have hcoord (i : Fin N) : Integrable (fun u : Fin N → Ω => X i (u i)) (Measure.pi (fun _ : Fin N => μ)) :=
    (measurePreserving_eval (fun _ : Fin N => μ) i).integrable_comp_of_integrable (hXI i)
  have hcoordmean (i : Fin N) : (∫ u : Fin N → Ω, X i (u i) ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
    have h := integral_map (μ := Measure.pi (fun _ : Fin N => μ)) (measurable_pi_apply i).aemeasurable
      (hXm i).aestronglyMeasurable
    rw [(measurePreserving_eval (fun _ : Fin N => μ) i).map_eq, hXmean i] at h
    exact h.symm
  have hYm : Measurable Y := Finset.measurable_fun_sum _ (fun i _ => (hXm i).comp (measurable_pi_apply i))
  have hYmean : (∫ u, Y u ∂Measure.pi (fun _ : Fin N => μ)) = 0 := by
    rw [show Y = (fun u => ∑ i, X i (u i)) from rfl, integral_finsetSum _ (fun i _ => hcoord i)]
    simp only [hcoordmean, Finset.sum_const_zero]
  have hrow (i : Fin N) : variance (X i) μ = (a i) ^ 2 * (μ.real A - (μ.real A) ^ 2) := by
    rw [show X i = (fun ω => a i * centeredIndicator A (μ.real A) ω) from rfl, variance_const_mul,
      variance_eq_integral (centeredIndicator_measurable hA _).aemeasurable]
    simp only [centeredIndicator_mean hA, sub_zero, centeredIndicator_secondMoment hA]
  have hvar := variance_sum_pi hXLp
  have he : variance Y (Measure.pi (fun _ : Fin N => μ)) = ∑ i, variance (X i) μ := by
    convert! hvar using 1
    congr 1
    funext u
    simp only [Y, Finset.sum_apply]
  have hev : variance Y (Measure.pi (fun _ : Fin N => μ)) =
      ∫ u, Y u ^ 2 ∂Measure.pi (fun _ : Fin N => μ) := by
    rw [variance_eq_integral hYm.aemeasurable, hYmean]
    simp only [sub_zero]
  change (∫ u, Y u ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) = _
  rw [← hev, he]
  simp_rw [hrow]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

lemma weighted_centeredIndicator_absoluteMean {A : Set Ω} (hA : MeasurableSet A) (a : Fin N → ℝ) :
    (∫ u : Fin N → Ω, |∑ i, a i * centeredIndicator A (μ.real A) (u i)|
      ∂Measure.pi (fun _ : Fin N => μ)) ≤
      Real.sqrt (μ.real A * (1 - μ.real A) * ∑ i, (a i) ^ 2) := by
  let Y : (Fin N → Ω) → ℝ := fun u => ∑ i, a i * centeredIndicator A (μ.real A) (u i)
  let C : ℝ := ∑ i, |a i|
  have hC : 0 ≤ C := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  have hm : Measurable Y := Finset.measurable_fun_sum _ (fun i _ =>
    ((centeredIndicator_measurable hA _).comp (measurable_pi_apply i)).const_mul _)
  have hb (u : Fin N → Ω) : |Y u| ≤ C := by
    calc
      _ ≤ ∑ i, |a i * centeredIndicator A (μ.real A) (u i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ C := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [abs_mul, mul_one] using mul_le_mul_of_nonneg_left
          (centeredIndicator_abs_le_one A measureReal_nonneg measureReal_le_one (u i)) (abs_nonneg (a i))
  have hma : Measurable (fun u => |Y u|) := continuous_abs.measurable.comp hm
  have hi (k : ℕ) := integrable_pow_of_bound (μ := Measure.pi (fun _ : Fin N => μ)) hma hC
    (Filter.Eventually.of_forall (fun u => by simpa only [abs_abs] using hb u)) k
  have hI : Integrable (fun u => |Y u|) (Measure.pi (fun _ : Fin N => μ)) := by
    convert! hi 1 using 1
    simp only [pow_one]
  have hj := Reach.sq_integral_le_integral_sq (Measure.pi (fun _ : Fin N => μ)) hI (hi 2)
  have he : (∫ u, |Y u| ^ 2 ∂Measure.pi (fun _ : Fin N => μ)) =
      μ.real A * (1 - μ.real A) * ∑ i, (a i) ^ 2 := by
    simp only [sq_abs]
    exact weighted_centeredIndicator_secondMoment μ hA a
  rw [he] at hj
  exact Real.le_sqrt_of_sq_le hj

end ProphetSecretary.Probability
