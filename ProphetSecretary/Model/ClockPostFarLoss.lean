import ProphetSecretary.Model.ClockNearLoss

/-!
# Post-entrance far-below-threshold time loss for actual continuation

Waiting gives v_z(t)≥z(1−t). Hence v_z<x/2 can occur only in a terminal
window of length x/(2lo), and a disagreement there requires E≥x/2.
The window estimate remains valid when its formal length exceeds one.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.clock_post_far_loss_integral_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo z x σ E : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hx : 0 < x)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hE : 0 ≤ E) (u : Fin n → ℝ) (loss : ℝ → ℝ)
    (hm : AEStronglyMeasurable loss (volume.restrict
      (Ioc σ 1 ∩ {t | P.clockContinuation z u t < x / 2})))
    (h0 : ∀ᵐ t ∂volume.restrict (Ioc σ 1 ∩ {t | P.clockContinuation z u t < x / 2}), 0 ≤ loss t)
    (hdom : ∀ᵐ t ∂volume.restrict (Ioc σ 1 ∩ {t | P.clockContinuation z u t < x / 2}),
      loss t ≤ ((Ioc σ 1 ∩ {t | P.clockContinuation z u t < x / 2}) ∩
        {t | |x - P.clockContinuation z u t| ≤ E}).indicator (fun _ => E) t) :
    (∫ t in Ioc σ 1 ∩ {t | P.clockContinuation z u t < x / 2}, loss t) ≤
      (x / (2 * lo)) * (if x / 2 ≤ E then E else 0) := by
  let S := Ioc σ 1 ∩ {t | P.clockContinuation z u t < x / 2}
  have hz : 0 < z := hlo.trans_le hloz
  have hV := P.measurable_clockContinuation hP hz.le u
  have hS : MeasurableSet S := measurableSet_Ioc.inter (measurableSet_lt hV measurable_const)
  have hS01 : S ⊆ Icc (0 : ℝ) 1 := fun _ ht => ⟨hσ.1.trans ht.1.1.le, ht.1.2⟩
  by_cases hlarge : x / 2 ≤ E
  · rw [if_pos hlarge]
    have hwindow : S ⊆ Icc (1 - x / (2 * lo)) 1 := by
      intro t ht
      have ht1 : t ≤ 1 := ht.1.2
      have hw := P.durationWeight_le_continuationValue hP (pendingClockSet t u)
        (sub_nonneg.mpr ht1) zero_le_one hz.le
      have hval : P.clockContinuation z u t < x / 2 := ht.2
      rw [P.clockContinuation_eq z u ht1] at hval
      have hcoef := mul_le_mul_of_nonneg_right hloz (sub_nonneg.mpr ht1)
      have hlt : lo * (1 - t) ≤ x / 2 := by linarith only [hcoef, hw, hval]
      have hd : 1 - t ≤ x / (2 * lo) := by
        apply (le_div_iff₀ (by positivity : 0 < 2 * lo)).mpr
        nlinarith only [hlt]
      exact ⟨by linarith only [hd], ht1⟩
    have hv : volume S < ⊤ := (measure_mono hS01).trans_lt (by simp [Real.volume_Icc])
    haveI : IsFiniteMeasure (volume.restrict S) := ⟨by simpa only [Measure.restrict_apply MeasurableSet.univ, univ_inter] using hv⟩
    have hbound : ∀ᵐ t ∂volume.restrict S, loss t ≤ E := by
      filter_upwards [hdom] with t ht
      apply ht.trans
      change (S ∩ {t | |x - P.clockContinuation z u t| ≤ E}).indicator (fun _ => E) t ≤ E
      by_cases hb : t ∈ S ∩ {t | |x - P.clockContinuation z u t| ≤ E}
      · simp only [Set.indicator_of_mem hb, le_refl]
      · simpa only [Set.indicator_of_notMem hb] using hE
    have hi : Integrable loss (volume.restrict S) := Integrable.of_bound hm E (by
      filter_upwards [h0, hbound] with t ht hb
      simpa only [Real.norm_eq_abs, abs_of_nonneg ht] using hb)
    have hint := integral_mono_ae hi (integrable_const E) hbound
    have hmeasure : volume.real S ≤ x / (2 * lo) := by
      have hR : volume (Icc (1 - x / (2 * lo)) 1) < ⊤ := by simp [Real.volume_Icc]
      have h := ENNReal.toReal_mono hR.ne (measure_mono hwindow)
      simpa only [Measure.real, Real.volume_Icc, sub_sub_cancel, ENNReal.toReal_ofReal (by positivity : 0 ≤ x / (2 * lo))] using h
    have hconst : (∫ _t in S, E) = volume.real S * E := by simp [integral_const, smul_eq_mul]
    change (∫ t in S, loss t) ≤ _
    rw [hconst] at hint
    exact hint.trans (mul_le_mul_of_nonneg_right hmeasure hE)
  · rw [if_neg hlarge, mul_zero]
    have hzero : loss =ᵐ[volume.restrict S] (fun _ => 0) := by
      filter_upwards [h0, hdom] with t ht hd
      have hnot : t ∉ S ∩ {t | |x - P.clockContinuation z u t| ≤ E} := by
        intro hb
        have hv : P.clockContinuation z u t < x / 2 := hb.1.2
        have he := (abs_le.mp (show |x - P.clockContinuation z u t| ≤ E from hb.2)).2
        linarith only [hv, he, not_le.mp hlarge]
      rw [Set.indicator_of_notMem hnot] at hd
      exact le_antisymm hd ht
    change (∫ t in S, loss t) ≤ _
    rw [integral_congr_ae hzero, integral_zero]

end ProphetSecretary.Model
