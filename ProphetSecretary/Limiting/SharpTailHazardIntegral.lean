import ProphetSecretary.Limiting.TailHazardIntegral
import ProphetSecretary.Limiting.SharpHorizonKernel

/-!
# Sharp integrated tail-intensity discrepancy

This proves `eq:tail-residual` with its exact π/2 coefficient. The earlier
integrable envelope supplies all Fubini obligations; the exact singular-kernel
integral sharpens the estimate without changing the order of integrations.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {N : ℕ}

lemma integral_mean_abs_tailHazardError_sharp_le (a : Fin N → ℝ) :
    (∫ t, ∫ u, |tailHazardError a t u| ∂Model.Instance.clocksLaw N ∂Model.Instance.uniformClock) ≤
      (Real.pi / 2) * Real.sqrt (∑ i, (a i) ^ 2) := by
  have hi := integral_mono_ae (integrable_mean_abs_tailHazardError a)
    (timeRatioKernel_integrable.const_mul (Real.sqrt (∑ i, (a i) ^ 2)))
    (Filter.Eventually.mono uniformClock_mem_Ioo (fun t ht => by
      simpa only [timeRatioKernel, mul_comm] using tailHazardError_absoluteMean_le a ht.1.le ht.2))
  rw [integral_const_mul, integral_timeRatioKernel] at hi
  simpa only [mul_comm] using hi

lemma integral_tailHazardIntegrand_clockTime_sharp_le (P : Model.Instance N) {x : ℝ} (hx : 0 ≤ x) :
    (∫ z : ℝ × (Fin N → ℝ), tailHazardIntegrand P (x, z)
      ∂Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)) ≤
      (Real.pi / 2) * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
  change (∫ z : ℝ × (Fin N → ℝ), |tailHazardError (distributionTail P x) z.1 z.2| ∂_) ≤ _
  rw [integral_prod _ (integrable_tailHazardError_product (distributionTail P x))]
  exact (integral_mean_abs_tailHazardError_sharp_le (distributionTail P x)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (distributionTail_sqSum_le P hx)) (by positivity))

lemma integral_tailHazardIntegrand_sharp_le (P : Model.Instance N) {H : ℝ} (hH : 0 ≤ H) :
    (∫ q, tailHazardIntegrand P q ∂(volume.restrict (Icc 0 H)).prod
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N))) ≤
      (Real.pi / 2) * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
  rw [integral_prod _ (integrable_tailHazardIntegrand P H)]
  have hi := integral_mono_ae (integrable_mean_tailHazardIntegrand P H)
    (integrable_const ((Real.pi / 2) * Real.sqrt (∑ i, distributionTail P 0 i ^ 2)))
    ((ae_restrict_mem measurableSet_Icc).mono (fun x hx => integral_tailHazardIntegrand_clockTime_sharp_le P hx.1))
  have hc : (∫ _x : ℝ, (Real.pi / 2) * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) ∂volume.restrict (Icc 0 H)) =
      (Real.pi / 2) * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
    simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal hH, smul_eq_mul]
    ring
  exact hi.trans_eq hc

/-- `eq:tail-residual`, in the manuscript's clocks/time/level integration order. -/
theorem expected_tailHazard_integral_sharp_le (P : Model.Instance N) {H : ℝ} (hH : 0 ≤ H) :
    (∫ u, ∫ t, ∫ x in Icc 0 H, |tailHazardError (distributionTail P x) t u|
      ∂volume ∂Model.Instance.uniformClock ∂Model.Instance.clocksLaw N) ≤
      (Real.pi / 2) * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
  let ν := volume.restrict (Icc (0 : ℝ) H)
  let U := Model.Instance.uniformClock
  let C := Model.Instance.clocksLaw N
  let F := tailHazardIntegrand P
  have hI : Integrable F (ν.prod (U.prod C)) := integrable_tailHazardIntegrand P H
  have hmp := measurePreserving_prodAssoc ν U C
  have hG : Integrable (fun q : (ℝ × ℝ) × (Fin N → ℝ) => F (q.1.1, (q.1.2, q.2))) ((ν.prod U).prod C) :=
    hmp.integrable_comp_of_integrable hI
  have hswap : (∫ u, ∫ t, ∫ x, F (x, (t, u)) ∂ν ∂U ∂C) = ∫ q, F q ∂ν.prod (U.prod C) := by
    calc
      _ = ∫ u, ∫ z : ℝ × ℝ, F (z.1, (z.2, u)) ∂ν.prod U ∂C := by
        apply integral_congr_ae
        filter_upwards [hG.prod_left_ae] with u hu
        exact (integral_prod_symm _ hu).symm
      _ = ∫ q : (ℝ × ℝ) × (Fin N → ℝ), F (q.1.1, (q.1.2, q.2)) ∂(ν.prod U).prod C :=
        (integral_prod_symm _ hG).symm
      _ = _ := by
        have h := integral_map (μ := (ν.prod U).prod C) hmp.measurable.aemeasurable
          (measurable_tailHazardIntegrand P).aestronglyMeasurable
        rw [hmp.map_eq] at h
        exact h.symm
  change (∫ u, ∫ t, ∫ x, F (x, (t, u)) ∂ν ∂U ∂C) ≤ _
  rw [hswap]
  exact integral_tailHazardIntegrand_sharp_le P hH

end ProphetSecretary.Limiting
