import ProphetSecretary.Stability.FirstDisagreement
import ProphetSecretary.Model.DurationLower

/-!
# Rewards in a terminal window

The terminal maximum uses every offer in the window, without conditioning on whether
any policy is still running. This proves the estimate used in
`eq:ps-reward-stability-explicit` for arbitrary policies and zero observations.
-/

open MeasureTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

lemma Instance.uniformClock_probability_ge {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    Instance.uniformClock.real (Ici s) = 1 - s := by
  have he : Ici s = (Iio s)ᶜ := by ext x; simp
  rw [he, measureReal_compl measurableSet_Iio, probReal_univ,
    Instance.uniformClock_probability_lt hs0 hs1]

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

lemma Instance.world_lateTail_probability (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (i : Fin n) {window : ℝ} (hw0 : 0 ≤ window) (hw1 : window ≤ 1) (d : ℝ) :
    (P.worldLaw ν).real {ω : World n Seed | 1 - window ≤ ω.2.1 i ∧ d < ω.1 i} =
      window * (P.law i (Ioi d)).toReal := by
  have hp : MeasurePreserving (fun ω : World n Seed => (ω.2.1 i, ω.1 i)) (P.worldLaw ν)
      (Instance.uniformClock.prod (P.law i)) :=
    Measure.measurePreserving_swap.comp (P.world_candidate_measurePreserving ν i)
  calc
    _ = ((P.worldLaw ν).map (fun ω : World n Seed => (ω.2.1 i, ω.1 i))).real
        (Ici (1 - window) ×ˢ Ioi d) :=
      (map_measureReal_apply hp.measurable (measurableSet_Ici.prod measurableSet_Ioi)).symm
    _ = (Instance.uniformClock.prod (P.law i)).real (Ici (1 - window) ×ˢ Ioi d) := by rw [hp.map_eq]
    _ = _ := by
      rw [measureReal_prod_prod, Instance.uniformClock_probability_ge (by linarith : 0 ≤ 1 - window)
        (by linarith : 1 - window ≤ 1)]
      change (1 - (1 - window)) * (P.law i (Ioi d)).toReal = _
      ring

lemma Instance.integrable_lateMaximum (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {H cut : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    Integrable (fun ω : World n Seed => lateMaximum ω.1 ω.2.1 cut) (P.worldLaw ν) := by
  have hm : Measurable (fun ω : World n Seed => lateMaximum ω.1 ω.2.1 cut) :=
    measurable_lateMaximum (fun i => (measurable_pi_apply i).comp measurable_fst)
      (fun i => (measurable_pi_apply i).comp (measurable_fst.comp measurable_snd)) measurable_const
  have hvals : ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ i, ω.1 i ≤ H := by
    have hv : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H := by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hbound i)
    exact (measurePreserving_fst : MeasurePreserving (fun ω : World n Seed => ω.1)
      (P.worldLaw ν) P.valuesLaw).quasiMeasurePreserving.ae hv
  apply Integrable.of_bound hm.aestronglyMeasurable H
  filter_upwards [hvals] with ω hω
  rw [Real.norm_eq_abs, abs_of_nonneg (lateMaximum_nonnegative _ _ _)]
  exact lateMaximum_le _ _ _ hH hω

/-- Uniform terminal-maximum bound from the expected tail count. -/
theorem Instance.integral_lateMaximum_le (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    {H d window : ℝ} (hH : 0 ≤ H) (hd : 0 ≤ d) (hw0 : 0 ≤ window) (hw1 : window ≤ 1)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    (∫ ω : World n Seed, lateMaximum ω.1 ω.2.1 (1 - window) ∂P.worldLaw ν) ≤
      d + H * window * P.tailCount d := by
  classical
  let μ := P.worldLaw ν
  let E : Fin n → Set (World n Seed) := fun i => {ω | 1 - window ≤ ω.2.1 i ∧ d < ω.1 i}
  let J : Fin n → World n Seed → ℝ := fun i ω => if ω ∈ E i then 1 else 0
  have hEm (i : Fin n) : MeasurableSet (E i) :=
    (measurableSet_le measurable_const ((measurable_pi_apply i).comp (measurable_fst.comp measurable_snd))).inter
      (measurableSet_lt measurable_const ((measurable_pi_apply i).comp measurable_fst))
  have hJI (i : Fin n) : Integrable (J i) μ := by
    apply Integrable.of_bound (Measurable.ite (hEm i) measurable_const measurable_const).aestronglyMeasurable 1
    filter_upwards [] with ω
    dsimp [J]
    split_ifs <;> norm_num
  have hJeq (i : Fin n) : (∫ ω, J i ω ∂μ) = window * (P.law i (Ioi d)).toReal := by
    have h : (∫ ω, J i ω ∂μ) = μ.real (E i) := by
      simpa only [J, Set.indicator_apply, Pi.one_apply] using (integral_indicator_one (μ := μ) (hEm i))
    exact h.trans (P.world_lateTail_probability ν i hw0 hw1 d)
  have hvals : ∀ᵐ ω : World n Seed ∂μ, ∀ i, ω.1 i ≤ H := by
    have hv : ∀ᵐ x ∂P.valuesLaw, ∀ i, x i ≤ H := by
      rw [ae_all_iff]
      intro i
      exact (measurePreserving_eval P.law i).quasiMeasurePreserving.ae (hbound i)
    exact (measurePreserving_fst : MeasurePreserving (fun ω : World n Seed => ω.1) μ P.valuesLaw).quasiMeasurePreserving.ae hv
  have hsum : Integrable (fun ω : World n Seed => ∑ i, J i ω) μ :=
    integrable_finsetSum Finset.univ (fun i _ => hJI i)
  have h := integral_mono_ae (P.integrable_lateMaximum ν hH hbound)
    ((integrable_const d).add (hsum.const_mul H)) (by
      filter_upwards [hvals] with ω hω
      exact lateMaximum_le_cutoff_add_tail_count ω.1 ω.2.1 hH hd hω)
  change (∫ ω : World n Seed, lateMaximum ω.1 ω.2.1 (1 - window) ∂μ) ≤
    ∫ ω : World n Seed, d + H * ∑ i, J i ω ∂μ at h
  rw [integral_add (f := fun _ : World n Seed => d) (g := fun ω : World n Seed => H * ∑ i, J i ω)
    (integrable_const d) (hsum.const_mul H), integral_const_mul,
    integral_finsetSum Finset.univ (fun i _ => hJI i)] at h
  simp only [integral_const, probReal_univ, one_smul, hJeq] at h
  have he : H * (∑ i, window * (P.law i (Ioi d)).toReal) = H * window * P.tailCount d := by
    rw [← Finset.mul_sum]
    unfold Instance.tailCount
    ring
  rwa [he] at h

end ProphetSecretary.Model
