import ProphetSecretary.Model.ClockAnnotations
import ProphetSecretary.Statistics.CalibratedCoefficientGrid

/-!
# A clock-rounded numerical continuation family

On continuous comparison trajectories, a rounded-clock query can be
expressed as a callback at the rounded remaining horizon. Its duration
floor is inserted into the callback. The prefix maximum then gives exactly
the same thresholds as the rank-preserving rounded-clock execution.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {PSeed : Type*}

noncomputable def clockRoundedEstimate (f : ℝ → ℝ)
    (estimate : ContinuationEstimator n m PSeed) : ContinuationEstimator n m PSeed :=
  fun q A u z r =>
    let v := unitRemaining (f (1-u))
    max (z*v) (estimate q A v z r)

lemma measurable_clockRoundedEstimate [MeasurableSpace PSeed] {f : ℝ → ℝ} (hf : Measurable f)
    (estimate : ContinuationEstimator n m PSeed)
    (he : Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2)) :
    Measurable (fun p : Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed))) =>
      clockRoundedEstimate f estimate p.1 p.2.1 p.2.2.1 p.2.2.2.1 p.2.2.2.2) := by
  let Ω := Reservoir n m × (Finset (Fin n) × (ℝ × (ℝ × PSeed)))
  have hu : Measurable (fun p : Ω => p.2.2.1) := by fun_prop
  have hz : Measurable (fun p : Ω => p.2.2.2.1) := by fun_prop
  have hv : Measurable (fun p : Ω => unitRemaining (f (1-p.2.2.1))) :=
    continuous_unitRemaining.measurable.comp (hf.comp ((measurable_const (a := (1 : ℝ))).sub hu))
  have hArg : Measurable (fun p : Ω => (p.1,p.2.1,unitRemaining (f (1-p.2.2.1)),p.2.2.2)) :=
    measurable_fst.prodMk ((by fun_prop : Measurable (fun p : Ω => p.2.1)).prodMk
      (hv.prodMk (by fun_prop)))
  have h := (hz.mul hv).max (he.comp hArg)
  convert h using 1
  funext p
  rfl

lemma continuationIdentities_annotateClockHistory (f : ℝ → ℝ) (q : Reservoir n m)
    (H : History n) (i : Fin n) :
    continuationIdentities q (annotateClockHistory f H) i=continuationIdentities q H i := by
  simp only [continuationIdentities,unseen_annotateClockHistory]

lemma familyThreshold_clockRounded {zlo zhi : ℝ} (hz0 : 0≤zlo) (hz : zlo≤zhi)
    (f : ℝ → ℝ) (estimate : ContinuationEstimator n m PSeed)
    (j : Fin (J+1)) (p : Reservoir n m × PolicyQueryArray n J PSeed)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) (hf : f t∈Icc (0 : ℝ) t)
    (i : Fin n) (H : History n) :
    familyThreshold zlo zhi (clockRoundedEstimate f estimate) j p t i H =
      familyThreshold zlo zhi estimate j p (f t) i (annotateClockHistory f H) := by
  let u := unitRemaining t
  let v := unitRemaining (f t)
  let z := familyCoefficient zlo zhi J
  let a := familyQuery zlo zhi (clockRoundedEstimate f estimate) p t i H
  let b := familyQuery zlo zhi estimate p (f t) i (annotateClockHistory f H)
  have hf1 : f t∈Icc (0 : ℝ) 1 := ⟨hf.1,hf.2.trans ht.2⟩
  have huv : u≤v := by dsimp [u,v]; rw [unitRemaining_eq ht,unitRemaining_eq hf1]; linarith [hf.2]
  have hv0 : 0≤v := (unitRemaining_range (f t)).1
  have hZ0 : 0≤z j.val := hz0.trans (familyCoefficient_range hz J j.val).1
  have hvEq : unitRemaining (f (1-unitRemaining t))=v := by
    rw [unitRemaining_eq ht,show 1-(1-t)=t by ring]
  have hab (k : ℕ) : a k=max (z k*v) (b k) := by
    simp only [a,b,z,familyQuery,clockRoundedEstimate,hvEq,
      continuationIdentities_annotateClockHistory,currentRankFromClock_annotateClockHistory,v]
  change ProphetSecretary.Statistics.nestedContinuation z a u j.val =
    ProphetSecretary.Statistics.nestedContinuation z b v j.val
  apply le_antisymm
  · apply max_le
    · exact (mul_le_mul_of_nonneg_left huv hZ0).trans
        (ProphetSecretary.Statistics.durationFloor_le_nestedContinuation z b v j.val)
    · apply Finset.sup'_le
      intro k hk
      rw [hab]
      have hkj : k≤j.val := Nat.le_of_lt_succ (Finset.mem_range.mp hk)
      apply max_le
      · exact (mul_le_mul_of_nonneg_right (familyCoefficient_monotone hz J hkj) hv0).trans
          (ProphetSecretary.Statistics.durationFloor_le_nestedContinuation z b v j.val)
      · exact (Finset.le_sup' b hk).trans (le_max_right _ _)
  · apply max_le
    · have h := ProphetSecretary.Statistics.estimate_le_nestedContinuation z a u j.val
      rw [hab] at h
      exact (le_max_left _ _).trans h
    · apply Finset.sup'_le
      intro k hk
      have h : a k≤ProphetSecretary.Statistics.nestedContinuation z a u j.val :=
        (Finset.le_sup' a hk).trans (le_max_right _ _)
      rw [hab] at h
      exact (le_max_right _ _).trans h

lemma numericalFamilyPolicy_clockRounded [NeZero m] {zlo zhi : ℝ} (hz0 : 0≤zlo) (hz : zlo≤zhi)
    (f : ℝ → ℝ) (estimate : ContinuationEstimator n m PSeed)
    (j : Fin (J+1)) (p : Reservoir n m × PolicyQueryArray n J PSeed)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) (hf : f t∈Icc (0 : ℝ) t)
    (i : Fin n) (x : ℝ) (H : History n) :
    (numericalFamilyPolicy zlo zhi (clockRoundedEstimate f estimate) j).decide p t i x H =
      ((numericalFamilyPolicy zlo zhi estimate j).withClockAnnotations f).decide p t i x H := by
  simp only [numericalFamilyPolicy,Policy.withClockAnnotations]
  split_ifs
  · rfl
  · simp only [cappedHistoryThresholdPolicy,familyThreshold_clockRounded hz0 hz f estimate j p ht hf i H]

/-- The clock change and the added duration floor preserve the same additive error budget. -/
lemma clockRoundedEstimate_error {z u v δ h estimate value value' : ℝ}
    (hz : 0≤z) (hh : 0≤h)
    (hu : v-u≤δ) (hFloor : z*u≤value)
    (hTime : |value'-value|≤z*δ) (hQuery : |estimate-value'|≤h) :
    |max (z*v) estimate-value|≤h+z*δ := by
  have hTime' := abs_le.mp hTime
  have hQ' := abs_le.mp hQuery
  apply abs_le.mpr
  constructor
  · have hm := le_max_right (z*v) estimate
    linarith only [hTime'.1,hQ'.1,hm]
  · have hDrift := mul_le_mul_of_nonneg_left hu hz
    have hUpper : max (z*v) estimate≤value+(h+z*δ) := by
      apply max_le
      · nlinarith only [hDrift,hFloor,hh]
      · linarith only [hTime'.2,hQ'.2]
    linarith only [hUpper]

end ProphetSecretary.Statistics.Calibration
