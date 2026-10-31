import ProphetSecretary.Model.ClockReciprocalSlope
import ProphetSecretary.Model.ScalarBands
import ProphetSecretary.Analysis.ReciprocalSlopeBand

/-!
# Near-threshold time loss for the actual continuation curve

The clipped horizon supplies a total measurable curve and agrees with the
physical remaining horizon on [0,1]. Actual continuation slopes, including
downward deletion jumps, give the near-region estimate with explicit constant
4(2+hi)/lo. All training randomness is held fixed during this time integral.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Model

open ProphetSecretary.Probability

variable {n : ℕ}

lemma measurable_pendingClockSet_time (u : Fin n → ℝ) : Measurable (fun t => pendingClockSet t u) := by
  rw [measurable_finset_iff]
  intro i
  apply measurableSet_setOf.mp
  simp only [mem_pendingClockSet]
  exact measurableSet_Iic

noncomputable def Instance.clockContinuation (P : Instance n) (z : ℝ) (u : Fin n → ℝ) (t : ℝ) : ℝ :=
  P.continuationValue (pendingClockSet t u) (max 0 (1 - t)) 1 z

lemma Instance.clockContinuation_eq (P : Instance n) (z : ℝ) (u : Fin n → ℝ) {t : ℝ} (ht : t ≤ 1) :
    P.clockContinuation z u t = P.continuationValue (pendingClockSet t u) (1 - t) 1 z := by
  unfold clockContinuation
  rw [max_eq_right (sub_nonneg.mpr ht)]

lemma Instance.measurable_clockContinuation (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {z : ℝ} (hz : 0 ≤ z) (u : Fin n → ℝ) :
    Measurable (P.clockContinuation z u) := by
  have hp : Measurable (fun t : ℝ => (pendingClockSet t u, t)) :=
    (measurable_pendingClockSet_time u).prodMk measurable_id
  change Measurable ((fun q : Finset (Fin n) × ℝ =>
    P.continuationValue q.1 (max 0 (1 - q.2)) 1 z) ∘ (fun t : ℝ => (pendingClockSet t u, t)))
  exact (P.measurable_stateElapsedValue hP zero_le_one hz).comp hp

/-- The actual near-region inequality used in `upstat:selected`. The size
multiplier is precisely the true remaining size at the entrance. -/
theorem Instance.clock_near_loss_integral_le (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lo hi z x σ E : ℝ}
    (hlo : 0 < lo) (hloz : lo ≤ z) (hzhi : z ≤ hi) (hx : 0 < x)
    (hσ : σ ∈ Icc (0 : ℝ) 1) (hE : 0 ≤ E) (u : Fin n → ℝ) (loss : ℝ → ℝ)
    (hm : AEStronglyMeasurable loss (volume.restrict
      (Icc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t})))
    (h0 : ∀ᵐ t ∂volume.restrict (Icc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}), 0 ≤ loss t)
    (hdom : ∀ᵐ t ∂volume.restrict (Icc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}),
      loss t ≤ ((Icc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}) ∩
        {t | |x - P.clockContinuation z u t| ≤ E}).indicator (fun _ => E) t) :
    (∫ t in Icc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}, loss t) ≤
      (4 * (2 + hi) / lo) * P.remainingSize σ u * E ^ 2 / x := by
  let S := Icc σ 1 ∩ {t | x / 2 ≤ P.clockContinuation z u t}
  let g := fun t => x - P.clockContinuation z u t
  let C := 2 * (2 + hi) / lo
  have hz : 0 < z := hlo.trans_le hloz
  have hhi : 0 < hi := hz.trans_le hzhi
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hB : 0 ≤ P.remainingSize σ u :=
    add_nonneg (P.restrictTo (pendingClockSet σ u)).totalFirstMoment_nonnegative (sub_nonneg.mpr hσ.2)
  have hV := P.measurable_clockContinuation hP hz.le u
  have hS : MeasurableSet S := measurableSet_Icc.inter (measurableSet_le measurable_const hV)
  have hS01 : S ⊆ Icc (0 : ℝ) 1 := fun _ ht => ⟨hσ.1.trans ht.1.1, ht.1.2⟩
  have hg : Measurable g := measurable_const.sub hV
  have hslope : ∀ t ∈ S, ∀ s ∈ S, t ≤ s →
      x * (s - t) ≤ C * P.remainingSize σ u * (g s - g t) := by
    intro t ht s hs hts
    have hf : x / 2 ≤ P.continuationValue (pendingClockSet s u) (1 - s) 1 z := by
      have hval : x / 2 ≤ P.clockContinuation z u s := hs.2
      rw [P.clockContinuation_eq z u hs.1.2] at hval
      exact hval
    have h := P.clockContinuation_reciprocalSlope hP hlo hloz hzhi hx hσ ht.1 hs.1 hts u hf
    rw [← P.clockContinuation_eq z u ht.1.2, ← P.clockContinuation_eq z u hs.1.2] at h
    change x * (s - t) ≤ C * P.remainingSize σ u * _
    convert h using 1
    dsimp [g]
    ring
  have hint := ProphetSecretary.Analysis.integral_reciprocalSlope_loss_le hS hS01 hx hC hB hE hg hslope hm h0 hdom
  have heq : 2 * C * P.remainingSize σ u * E ^ 2 / x =
      (4 * (2 + hi) / lo) * P.remainingSize σ u * E ^ 2 / x := by dsimp [C]; ring
  exact hint.trans_eq heq

end ProphetSecretary.Model
