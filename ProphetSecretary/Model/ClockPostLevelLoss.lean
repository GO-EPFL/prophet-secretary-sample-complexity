import ProphetSecretary.Model.ClockNearLoss
import ProphetSecretary.Model.ClockPostReciprocalSlope

/-!
# Post-entrance level losses

The early dyadic bands have a value floor determined by the band level, while
the disagreement is centered at the original candidate value x. Separating
these two parameters gives the actual time-integral estimate used there.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

theorem Instance.clock_post_level_loss_integral_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi z x σ E b : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hzhi : z ≤ hi) (hb : 0 < b)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hE : 0 ≤ E) (u : Fin n → ℝ)
    {S : Set ℝ} (hS : MeasurableSet S) (hSσ : S ⊆ Ioc σ 1)
    (hfloor : ∀ t ∈ S, b ≤ P.clockContinuation z u t) (loss : ℝ → ℝ)
    (hm : AEStronglyMeasurable loss (volume.restrict S))
    (h0 : ∀ᵐ t ∂volume.restrict S, 0 ≤ loss t)
    (hdom : ∀ᵐ t ∂volume.restrict S,
      loss t ≤ (S ∩ {t | |x - P.clockContinuation z u t| ≤ E}).indicator (fun _ => E) t) :
    (∫ t in S, loss t) ≤ (2 * (2 + hi) / lo) * P.postRemainingSize σ u * E ^ 2 / b := by
  let g := fun t => x - P.clockContinuation z u t
  let C := 2 * (2 + hi) / lo
  have hz : 0 < z := hlo.trans_le hloz
  have hhi : 0 < hi := hz.trans_le hzhi
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ P.postRemainingSize σ u :=
    (P.postRemainingSize_mem hσ.1 hσ.2 u).1
  have hS01 : S ⊆ Icc (0 : ℝ) 1 := fun t ht => ⟨hσ.1.trans (hSσ ht).1.le, (hSσ ht).2⟩
  have hg : Measurable g := measurable_const.sub (P.measurable_clockContinuation hP hz.le u)
  have hslope : ∀ t ∈ S, ∀ s ∈ S, t ≤ s →
      (2 * b) * (s - t) ≤ C * P.postRemainingSize σ u * (g s - g t) := by
    intro t ht s hs hts
    have hf : (2 * b) / 2 ≤ P.continuationValue (pendingClockSet s u) (1 - s) 1 z := by
      have hval := hfloor s hs
      rw [P.clockContinuation_eq z u (hSσ hs).2] at hval
      nlinarith only [hval]
    have h := P.clockContinuation_post_reciprocalSlope hP hlo hloz hzhi (by positivity : 0 < 2 * b)
      hσ (hSσ ht) (hSσ hs) hts u hf
    rw [← P.clockContinuation_eq z u (hSσ ht).2, ← P.clockContinuation_eq z u (hSσ hs).2] at h
    change (2 * b) * (s - t) ≤ C * P.postRemainingSize σ u * _
    convert h using 1
    dsimp [g]
    ring
  have h := ProphetSecretary.Analysis.integral_reciprocalSlope_loss_le hS hS01
    (by positivity : 0 < 2 * b) hC hB hE hg hslope hm h0 hdom
  have heq : 2 * C * P.postRemainingSize σ u * E ^ 2 / (2 * b) =
      (2 * (2 + hi) / lo) * P.postRemainingSize σ u * E ^ 2 / b := by dsimp [C]; ring
  exact h.trans_eq heq

/-- Near-region specialization with the actual post-entrance size. -/
theorem Instance.clock_post_near_loss_integral_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi z x σ E : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hzhi : z ≤ hi) (hx : 0 < x)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hE : 0 ≤ E) (u : Fin n → ℝ) (loss : ℝ → ℝ)
    (hm : AEStronglyMeasurable loss (volume.restrict
      (Ioc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t})))
    (h0 : ∀ᵐ t ∂volume.restrict (Ioc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}), 0 ≤ loss t)
    (hdom : ∀ᵐ t ∂volume.restrict (Ioc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}),
      loss t ≤ ((Ioc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}) ∩
        {t | |x - P.clockContinuation z u t| ≤ E}).indicator (fun _ => E) t) :
    (∫ t in Ioc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}, loss t) ≤
      (4 * (2 + hi) / lo) * P.postRemainingSize σ u * E ^ 2 / x := by
  let S := Ioc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}
  have hz : 0 < z := hlo.trans_le hloz
  have hV := P.measurable_clockContinuation hP hz.le u
  have hS : MeasurableSet S := measurableSet_Ioc.inter (measurableSet_le measurable_const hV)
  have h := P.clock_post_level_loss_integral_le hP hlo hloz hzhi
    (by positivity : 0 < x / 2) hσ hE u hS (fun _ ht => ht.1) (fun _ ht => ht.2) loss hm h0 hdom
  have heq : (2 * (2 + hi) / lo) * P.postRemainingSize σ u * E ^ 2 / (x / 2) =
      (4 * (2 + hi) / lo) * P.postRemainingSize σ u * E ^ 2 / x := by ring
  exact h.trans_eq heq

end ProphetSecretary.Model
