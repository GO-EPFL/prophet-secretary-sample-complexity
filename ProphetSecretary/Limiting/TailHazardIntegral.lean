import ProphetSecretary.Limiting.HazardIntegral

/-!
# Integrated tail-intensity discrepancy

The tail weights are fixed distributional quantities and the clocks are an
independent product of uniforms. Tonelli and Fubini obligations are discharged
before changing the order of level, elapsed-time, and clock integrations.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {N : ℕ}

noncomputable def distributionTail (P : Model.Instance N) (x : ℝ) (i : Fin N) : ℝ := (P.law i).real (Ioi x)

lemma measurable_distributionTail (P : Model.Instance N) (i : Fin N) :
    Measurable (fun x => distributionTail P x i) := by
  have ha : Antitone (fun x => distributionTail P x i) := by
    intro x y hxy
    exact ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun _ hx => hxy.trans_lt hx))
  exact ha.measurable

lemma distributionTail_sqSum_le (P : Model.Instance N) {x : ℝ} (hx : 0 ≤ x) :
    (∑ i, distributionTail P x i ^ 2) ≤ ∑ i, distributionTail P 0 i ^ 2 := by
  apply Finset.sum_le_sum
  intro i _
  have hle : distributionTail P x i ≤ distributionTail P 0 i :=
    ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono (fun _ hy => hx.trans_lt hy))
  exact (sq_le_sq₀ measureReal_nonneg measureReal_nonneg).mpr hle

noncomputable def tailHazardIntegrand (P : Model.Instance N) (q : ℝ × (ℝ × (Fin N → ℝ))) : ℝ :=
  |tailHazardError (distributionTail P q.1) q.2.1 q.2.2|

lemma measurable_tailHazardIntegrand (P : Model.Instance N) : Measurable (tailHazardIntegrand P) := by
  have hm (i : Fin N) : Measurable (fun q : ℝ × (ℝ × (Fin N → ℝ)) => distributionTail P q.1 i) :=
    (measurable_distributionTail P i).comp measurable_fst
  have hs : Measurable (fun q : ℝ × (ℝ × (Fin N → ℝ)) =>
      ∑ i, if q.2.1 < q.2.2 i then distributionTail P q.1 i else 0) := by
    apply Finset.measurable_fun_sum
    intro i _
    exact Measurable.ite (measurableSet_lt (measurable_fst.comp measurable_snd)
      ((measurable_pi_apply i).comp (measurable_snd.comp measurable_snd))) (hm i) measurable_const
  have hsum : Measurable (fun q : ℝ × (ℝ × (Fin N → ℝ)) => ∑ i, distributionTail P q.1 i) :=
    Finset.measurable_fun_sum _ (fun i _ => hm i)
  exact continuous_abs.measurable.comp
    ((hs.div (measurable_const.sub (measurable_fst.comp measurable_snd))).sub hsum)

lemma integral_tailHazardIntegrand_clockTime_le (P : Model.Instance N) {x : ℝ} (hx : 0 ≤ x) :
    (∫ z : ℝ × (Fin N → ℝ), tailHazardIntegrand P (x, z)
      ∂Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)) ≤
      2 * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
  change (∫ z : ℝ × (Fin N → ℝ), |tailHazardError (distributionTail P x) z.1 z.2| ∂_) ≤ _
  rw [integral_prod _ (integrable_tailHazardError_product (distributionTail P x))]
  exact (integral_mean_abs_tailHazardError_le (distributionTail P x)).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (distributionTail_sqSum_le P hx)) (by norm_num))

lemma integrable_mean_tailHazardIntegrand (P : Model.Instance N) (H : ℝ) :
    Integrable (fun x => ∫ z, tailHazardIntegrand P (x, z)
      ∂Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)) (volume.restrict (Icc 0 H)) := by
  have hm : StronglyMeasurable (fun x => ∫ z, tailHazardIntegrand P (x, z)
      ∂Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)) :=
    (measurable_tailHazardIntegrand P).stronglyMeasurable.integral_prod_right'
  apply Integrable.of_bound hm.aestronglyMeasurable (2 * Real.sqrt (∑ i, distributionTail P 0 i ^ 2))
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  have hn : 0 ≤ ∫ z, tailHazardIntegrand P (x, z)
      ∂Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N) := integral_nonneg (fun _ => abs_nonneg _)
  rw [Real.norm_eq_abs, abs_of_nonneg hn]
  exact integral_tailHazardIntegrand_clockTime_le P hx.1

lemma integrable_tailHazardIntegrand (P : Model.Instance N) (H : ℝ) :
    Integrable (tailHazardIntegrand P) ((volume.restrict (Icc 0 H)).prod
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N))) := by
  apply (integrable_prod_iff (measurable_tailHazardIntegrand P).aestronglyMeasurable).mpr
  constructor
  · exact Filter.Eventually.of_forall (fun x => integrable_tailHazardError_product (distributionTail P x))
  · simpa only [Real.norm_eq_abs, tailHazardIntegrand, abs_abs] using integrable_mean_tailHazardIntegrand P H

lemma integral_tailHazardIntegrand_le (P : Model.Instance N) {H : ℝ} (hH : 0 ≤ H) :
    (∫ q, tailHazardIntegrand P q ∂(volume.restrict (Icc 0 H)).prod
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N))) ≤
      2 * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
  rw [integral_prod _ (integrable_tailHazardIntegrand P H)]
  have hi := integral_mono_ae (integrable_mean_tailHazardIntegrand P H)
    (integrable_const (2 * Real.sqrt (∑ i, distributionTail P 0 i ^ 2)))
    ((ae_restrict_mem measurableSet_Icc).mono (fun x hx => integral_tailHazardIntegrand_clockTime_le P hx.1))
  have hc : (∫ _x : ℝ, 2 * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) ∂volume.restrict (Icc 0 H)) =
      2 * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
    simp only [integral_const, measureReal_def, Measure.restrict_apply_univ, Real.volume_Icc, sub_zero,
      ENNReal.toReal_ofReal hH, smul_eq_mul]
    ring
  exact hi.trans_eq hc

/-- Expected integrated error in the order used for the stopped drift estimate. -/
lemma expected_tailHazard_integral_le (P : Model.Instance N) {H : ℝ} (hH : 0 ≤ H) :
    (∫ u, ∫ t, ∫ x in Icc 0 H, |tailHazardError (distributionTail P x) t u|
      ∂volume ∂Model.Instance.uniformClock ∂Model.Instance.clocksLaw N) ≤
      2 * H * Real.sqrt (∑ i, distributionTail P 0 i ^ 2) := by
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
  exact integral_tailHazardIntegrand_le P hH

end ProphetSecretary.Limiting
