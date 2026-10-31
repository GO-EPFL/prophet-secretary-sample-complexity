import ProphetSecretary.Model.Independence

/-!
# Compensation identity for one independent uniform clock

Integrating the unseen-clock rate `1/(1-t)` against the probability of remaining
unseen gives one. The identity is nonnegative and therefore needs no boundedness
or integrability assumption on its test premium.
-/

open MeasureTheory Set
open scoped ENNReal Classical

namespace ProphetSecretary.Probability

lemma uniformClock_tail {t : ℝ} (ht0 : 0 ≤ t) :
    Model.Instance.uniformClock (Ioi t) = ENNReal.ofReal (1 - t) := by
  have he : Ioi t ∩ Icc (0 : ℝ) 1 = Ioc t 1 := by
    ext u
    constructor
    · rintro ⟨htu, _, hu1⟩
      exact ⟨htu, hu1⟩
    · rintro ⟨htu, hu1⟩
      exact ⟨htu, ht0.trans htu.le, hu1⟩
  rw [Model.Instance.uniformClock, Measure.restrict_apply measurableSet_Ioi, he, Real.volume_Ioc]

lemma uniformClock_mem_open_unit : ∀ᵐ t : ℝ ∂Model.Instance.uniformClock, t ∈ Ioo (0 : ℝ) 1 := by
  filter_upwards [ae_restrict_mem measurableSet_Icc, Model.Instance.uniformClock.ae_ne 0,
    Model.Instance.uniformClock.ae_ne 1] with t ht h0 h1
  exact ⟨lt_of_le_of_ne ht.1 h0.symm, lt_of_le_of_ne ht.2 h1⟩

noncomputable def uniformHazardKernel (g : ℝ → ℝ≥0∞) (s : ℝ) (q : ℝ × ℝ) : ℝ≥0∞ :=
  if q.2 ≤ s ∧ q.2 < q.1 then g q.2 / ENNReal.ofReal (1 - q.2) else 0

lemma measurable_uniformHazardKernel (g : ℝ → ℝ≥0∞) (hg : Measurable g) (s : ℝ) :
    Measurable (uniformHazardKernel g s) := by
  exact Measurable.ite ((measurableSet_le measurable_snd measurable_const).inter
    (measurableSet_lt measurable_snd measurable_fst))
    ((hg.comp measurable_snd).div (measurable_const.sub measurable_snd).ennreal_ofReal) measurable_const

/-- A fresh uniform clock exactly compensates its own rate while unseen. -/
lemma lintegral_uniform_hazard (g : ℝ → ℝ≥0∞) (hg : Measurable g) (s : ℝ) :
    (∫⁻ u, ∫⁻ t, uniformHazardKernel g s (u, t) ∂Model.Instance.uniformClock ∂Model.Instance.uniformClock) =
      ∫⁻ t, if t ≤ s then g t else 0 ∂Model.Instance.uniformClock := by
  have hm := measurable_uniformHazardKernel g hg s
  rw [← lintegral_prod _ hm.aemeasurable, lintegral_prod_symm _ hm.aemeasurable]
  apply lintegral_congr_ae
  filter_upwards [uniformClock_mem_open_unit] with t ht
  by_cases hts : t ≤ s
  · have he : (fun u => uniformHazardKernel g s (u, t)) =
        (Ioi t).indicator (fun _ => g t / ENNReal.ofReal (1 - t)) := by
      funext u
      simp [uniformHazardKernel, hts, Set.indicator_apply]
    rw [he, lintegral_indicator measurableSet_Ioi, lintegral_const,
      Measure.restrict_apply_univ, uniformClock_tail ht.1.le, if_pos hts]
    have hd0 : ENNReal.ofReal (1 - t) ≠ 0 := ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr ht.2))
    exact ENNReal.div_mul_cancel hd0 ENNReal.ofReal_ne_top
  · simp [uniformHazardKernel, hts]

end ProphetSecretary.Probability
