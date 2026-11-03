import ProphetSecretary.Statistics.CalibrationInterpolation
import ProphetSecretary.Statistics.DurationCalibration
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.MeasureTheory.Order.Group.Lattice

/-!
# Ordered duration curves from finitely many policy durations

A finite ramp sum continuously joins the knots, with constant extension
outside the unit parameter interval. Its formula on each segment is exactly
the endpoint mixture in `eq:calibration-duration-curve`.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Statistics.Calibration

noncomputable def unitRamp (t : ℝ) : ℝ := max 0 (min 1 t)

lemma unitRamp_range (t : ℝ) : unitRamp t ∈ Icc (0 : ℝ) 1 :=
  ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩

lemma continuous_unitRamp : Continuous unitRamp := by unfold unitRamp; fun_prop

lemma unitRamp_monotone : Monotone unitRamp := by
  intro s t hst
  exact max_le_max le_rfl (min_le_min le_rfl hst)

lemma unitRamp_of_nonpos {t : ℝ} (ht : t ≤ 0) : unitRamp t = 0 := by
  exact max_eq_left ((min_le_right _ _).trans ht)

lemma unitRamp_of_one_le {t : ℝ} (ht : 1 ≤ t) : unitRamp t = 1 := by
  simp only [unitRamp, min_eq_left ht, max_eq_right (by norm_num : (0 : ℝ) ≤ 1)]

lemma unitRamp_eq {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) : unitRamp t = t := by
  rw [unitRamp, min_eq_right ht.2, max_eq_right ht.1]

/-- The piecewise linear interpolation of `v 0,...,v N`, extended constantly. -/
noncomputable def durationCurve (N : ℕ) (v : ℕ → ℝ) (θ : ℝ) : ℝ :=
  v 0+∑ k ∈ Finset.range N, (v (k+1)-v k)*unitRamp ((N : ℝ)*θ-(k : ℝ))

lemma durationCurve_continuous (N : ℕ) (v : ℕ → ℝ) : Continuous (durationCurve N v) := by
  exact continuous_const.add (continuous_finsetSum _ (fun k _ =>
    continuous_const.mul (continuous_unitRamp.comp (by fun_prop))))

lemma durationCurve_monotone (N : ℕ) (v : ℕ → ℝ) (hv : Monotone v) : Monotone (durationCurve N v) := by
  intro s t hst
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k _
  have hDiff : 0 ≤ v (k+1)-v k := sub_nonneg.mpr (hv (Nat.le_succ k))
  apply mul_le_mul_of_nonneg_left _ hDiff
  apply unitRamp_monotone
  nlinarith [mul_le_mul_of_nonneg_left hst (Nat.cast_nonneg N)]

lemma durationCurve_zero (N : ℕ) (v : ℕ → ℝ) : durationCurve N v 0=v 0 := by
  unfold durationCurve
  have h (k : ℕ) : unitRamp (-(k : ℝ))=0 :=
    unitRamp_of_nonpos (neg_nonpos.mpr (Nat.cast_nonneg k))
  simp only [mul_zero, zero_sub, h, Finset.sum_const_zero, add_zero]

lemma durationCurve_one (N : ℕ) (v : ℕ → ℝ) : durationCurve N v 1=v N := by
  unfold durationCurve
  have h : ∑ k ∈ Finset.range N, (v (k+1)-v k)*unitRamp ((N : ℝ)*1-(k : ℝ)) =
      ∑ k ∈ Finset.range N, (v (k+1)-v k) := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' : (k : ℝ)+1 ≤ N := by exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
    rw [unitRamp_of_one_le (by linarith), mul_one]
  rw [h, Finset.sum_range_sub]
  ring

lemma durationCurve_range (N : ℕ) (v : ℕ → ℝ) (hv : Monotone v) (h0 : v 0=0) (h1 : v N=1)
    (θ : ℝ) : durationCurve N v θ ∈ Icc (0 : ℝ) 1 := by
  have hLow : 0 ≤ durationCurve N v θ := by
    unfold durationCurve
    rw [h0, zero_add]
    exact Finset.sum_nonneg (fun k _ => mul_nonneg
      (sub_nonneg.mpr (hv (Nat.le_succ k))) (unitRamp_range _).1)
  have hUp : durationCurve N v θ ≤ v 0+∑ k ∈ Finset.range N, (v (k+1)-v k) := by
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro k _
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (unitRamp_range _).2
      (sub_nonneg.mpr (hv (Nat.le_succ k)))
  rw [Finset.sum_range_sub, h0, h1] at hUp
  exact ⟨hLow, by linarith⟩

lemma measurable_durationCurve {Ω : Type*} [MeasurableSpace Ω] (N : ℕ)
    {v : Ω → ℕ → ℝ} {θ : Ω → ℝ}
    (hv : ∀ k, Measurable (fun ω => v ω k)) (hθ : Measurable θ) :
    Measurable (fun ω => durationCurve N (v ω) (θ ω)) := by
  exact (hv 0).add (Finset.measurable_sum _ (fun k _ => ((hv (k+1)).sub (hv k)).mul
    (continuous_unitRamp.measurable.comp ((measurable_const.mul hθ).sub_const _))))

/-- Exact agreement with linear interpolation on any knot segment. -/
lemma durationCurve_on_segment (N : ℕ) (hN : 0 < N) (v : ℕ → ℝ)
    (j : ℕ) (hj : j < N) {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) :
    durationCurve N v (((j : ℝ)+α)/(N : ℝ))=(1-α)*v j+α*v (j+1) := by
  have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  have hTime : (N : ℝ)*(((j : ℝ)+α)/(N : ℝ))=(j : ℝ)+α := by field_simp
  have hPrefix : ∑ k ∈ Finset.range j,
      (v (k+1)-v k)*unitRamp ((N : ℝ)*(((j : ℝ)+α)/(N : ℝ))-(k : ℝ)) = v j-v 0 := by
    calc
      _ = ∑ k ∈ Finset.range j, (v (k+1)-v k) := by
        apply Finset.sum_congr rfl
        intro k hk
        have hk' : (k : ℝ)+1 ≤ j := by exact_mod_cast Nat.succ_le_iff.mpr (Finset.mem_range.mp hk)
        rw [hTime, unitRamp_of_one_le (by linarith [hα.1]), mul_one]
      _ = _ := Finset.sum_range_sub v j
  have hMiddle : unitRamp ((N : ℝ)*(((j : ℝ)+α)/(N : ℝ))-(j : ℝ))=α := by
    rw [hTime]
    have he : (j : ℝ)+α-(j : ℝ)=α := by ring
    rw [he, unitRamp_eq hα]
  have hSuffix : ∑ k ∈ Finset.Ico (j+1) N,
      (v (k+1)-v k)*unitRamp ((N : ℝ)*(((j : ℝ)+α)/(N : ℝ))-(k : ℝ))=0 := by
    apply Finset.sum_eq_zero
    intro k hk
    have hk' : (j : ℝ)+1 ≤ k := by exact_mod_cast (Finset.mem_Ico.mp hk).1
    rw [hTime, unitRamp_of_nonpos (by linarith [hα.2]), mul_zero]
  unfold durationCurve
  rw [← Finset.sum_range_add_sum_Ico _ (Nat.succ_le_iff.mpr hj), Finset.sum_range_succ,
    hPrefix, hMiddle, hSuffix]
  ring

lemma durationCurve_add (N : ℕ) (v w : ℕ → ℝ) (θ : ℝ) :
    durationCurve N (fun k => v k+w k) θ=durationCurve N v θ+durationCurve N w θ := by
  unfold durationCurve
  have he (k : ℕ) : ((v (k+1)+w (k+1))-(v k+w k))*unitRamp ((N : ℝ)*θ-k) =
      (v (k+1)-v k)*unitRamp ((N : ℝ)*θ-k)+(w (k+1)-w k)*unitRamp ((N : ℝ)*θ-k) := by ring
  simp_rw [he, Finset.sum_add_distrib]
  ring

lemma durationCurve_const_mul (N : ℕ) (c : ℝ) (v : ℕ → ℝ) (θ : ℝ) :
    durationCurve N (fun k => c*v k) θ=c*durationCurve N v θ := by
  unfold durationCurve
  rw [mul_add, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring

lemma durationCurve_finset_sum {ι : Type*} (N : ℕ) (s : Finset ι) (v : ι → ℕ → ℝ) (θ : ℝ) :
    durationCurve N (fun k => ∑ i ∈ s, v i k) θ=∑ i ∈ s, durationCurve N (v i) θ := by
  induction s using Finset.induction_on with
  | empty => simp [durationCurve]
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    rw [durationCurve_add, ih]

/-- Averaging validation profiles commutes exactly with the surrogate curve. -/
lemma durationCurve_average (N m : ℕ) (v : Fin m → ℕ → ℝ) (θ : ℝ) :
    durationCurve N (fun k => (m : ℝ)⁻¹*∑ j, v j k) θ =
      (m : ℝ)⁻¹*∑ j, durationCurve N (v j) θ := by
  rw [durationCurve_const_mul, durationCurve_finset_sum]

end ProphetSecretary.Statistics.Calibration
