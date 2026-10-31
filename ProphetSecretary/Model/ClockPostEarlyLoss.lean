import ProphetSecretary.Model.ClockPostLevelLoss
import ProphetSecretary.Model.ContinuationCoefficientRatio

/-!
# Post-entrance earlier-band losses for the actual continuation curve

On v_hi≥a, the scalar comparison gives v_z≥a/R₀. For x≤a/(4R₀), a
disagreement requires E≥a/(2R₀). Integrating the actual reciprocal slope then
gives the B E²/a tail bound used before sixth moments in `upstat:selected`.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.clock_post_early_loss_integral_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi z x σ E a : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hzhi : z ≤ hi) (ha : 0 < a)
    (hx : x ≤ a / (4 * (hi / lo))) (hσ : σ ∈ Icc (0 : ℝ) 1) (hE : 0 ≤ E)
    (u : Fin n → ℝ) (loss : ℝ → ℝ)
    (hm : AEStronglyMeasurable loss (volume.restrict (Ioc σ 1 ∩ {t | a ≤ P.clockContinuation hi u t})))
    (h0 : ∀ᵐ t ∂volume.restrict (Ioc σ 1 ∩ {t | a ≤ P.clockContinuation hi u t}), 0 ≤ loss t)
    (hdom : ∀ᵐ t ∂volume.restrict (Ioc σ 1 ∩ {t | a ≤ P.clockContinuation hi u t}),
      loss t ≤ ((Ioc σ 1 ∩ {t | a ≤ P.clockContinuation hi u t}) ∩
        {t | |x - P.clockContinuation z u t| ≤ E}).indicator (fun _ => E) t) :
    (∫ t in Ioc σ 1 ∩ {t | a ≤ P.clockContinuation hi u t}, loss t) ≤
      (2 * (2 + hi) / lo) * (hi / lo) * P.postRemainingSize σ u *
        (if a / (2 * (hi / lo)) ≤ E then E ^ 2 else 0) / a := by
  let R := hi / lo
  let b := a / R
  let S := Ioc σ 1 ∩ {t | a ≤ P.clockContinuation hi u t}
  have hz : 0 < z := hlo.trans_le hloz
  have hhi : 0 < hi := hz.trans_le hzhi
  have hR : 0 < R := div_pos hhi hlo
  have hb : 0 < b := div_pos ha hR
  have hx' : x ≤ b / 4 := by
    convert hx using 1
    dsimp [b, R]
    ring
  have hthreshold : a / (2 * (hi / lo)) = b / 2 := by dsimp [b, R]; ring
  have hfloor (t : ℝ) (ht : t ∈ S) : b ≤ P.clockContinuation z u t := by
    have hv : a ≤ P.clockContinuation hi u t := ht.2
    have hr := P.clockContinuation_coefficient_ratio hP hlo hloz hzhi u t
    change P.clockContinuation hi u t ≤ R * P.clockContinuation z u t at hr
    change a / R ≤ _
    apply (div_le_iff₀ hR).mpr
    nlinarith only [hv, hr]
  have hV := P.measurable_clockContinuation hP hhi.le u
  have hS : MeasurableSet S := measurableSet_Ioc.inter (measurableSet_le measurable_const hV)
  rw [hthreshold]
  by_cases hlarge : b / 2 ≤ E
  · rw [if_pos hlarge]
    have hint := P.clock_post_level_loss_integral_le hP hlo hloz hzhi hb hσ hE u hS
      (fun _ ht => ht.1) hfloor loss hm h0 hdom
    have heq : (2 * (2 + hi) / lo) * P.postRemainingSize σ u * E ^ 2 / b =
        (2 * (2 + hi) / lo) * (hi / lo) * P.postRemainingSize σ u * E ^ 2 / a := by
      dsimp [b, R]
      field_simp
    exact hint.trans_eq heq
  · rw [if_neg hlarge, mul_zero, zero_div]
    have hzero : loss =ᵐ[volume.restrict S] (fun _ => 0) := by
      filter_upwards [h0, hdom] with t ht hd
      have hnot : t ∉ S ∩ {t | |x - P.clockContinuation z u t| ≤ E} := by
        intro hs
        have hv := hfloor t hs.1
        have he := (abs_le.mp (show |x - P.clockContinuation z u t| ≤ E from hs.2)).1
        linarith only [hv, he, hx', not_le.mp hlarge, hb]
      rw [Set.indicator_of_notMem hnot] at hd
      exact le_antisymm hd ht
    change (∫ t in S, loss t) ≤ _
    rw [integral_congr_ae hzero, integral_zero]

end ProphetSecretary.Model
