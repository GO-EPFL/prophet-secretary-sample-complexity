import ProphetSecretary.Model.ClockPostEarlyLoss
import ProphetSecretary.Analysis.MomentTailBound

/-!
# Post-entrance sixth-moment form of the actual early-band time loss

The proved disagreement threshold E≥a/(2R₀) changes the time-integral bound
from BE²/a into an explicit multiple of BE⁶/a⁵. No independence between the
entrance size and the error is used.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

variable {n : ℕ}

theorem Instance.clock_post_early_loss_integral_sixth_le (P : Instance n)
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
      (32 * (2 + hi) / lo) * (hi / lo) ^ 5 * P.postRemainingSize σ u * E ^ 6 / a ^ 5 := by
  have hz : 0 < z := hlo.trans_le hloz
  have hhi : 0 < hi := hz.trans_le hzhi
  have hR : 0 < hi / lo := div_pos hhi hlo
  have hB : 0 ≤ P.postRemainingSize σ u :=
    (P.postRemainingSize_mem hσ.1 hσ.2 u).1
  have htime := P.clock_post_early_loss_integral_le hP hlo hloz hzhi ha hx hσ hE u loss hm h0 hdom
  have htail := ProphetSecretary.Analysis.pow_tail_le_higherMoment hE
    (by positivity : 0 < a / (2 * (hi / lo))) (by decide : (2 : ℕ) ≤ 6)
  have hscaled := div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left htail
      (by positivity : 0 ≤ (2 * (2 + hi) / lo) * (hi / lo) * P.postRemainingSize σ u)) ha.le
  have heq : ((2 * (2 + hi) / lo) * (hi / lo) * P.postRemainingSize σ u) *
      (E ^ 6 / (a / (2 * (hi / lo))) ^ 4) / a =
      (32 * (2 + hi) / lo) * (hi / lo) ^ 5 * P.postRemainingSize σ u * E ^ 6 / a ^ 5 := by
    field_simp
    ring
  exact htime.trans (hscaled.trans_eq heq)

end ProphetSecretary.Model
