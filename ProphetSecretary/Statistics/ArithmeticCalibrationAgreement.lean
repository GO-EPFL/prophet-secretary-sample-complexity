import ProphetSecretary.Statistics.ArithmeticLearningWork

/-!
# Arithmetic execution and the calibrated policy

The sorted validation profiles give the same durations as the clock
policy on distinct clocks in the unit interval. Thus the counted
preparation uses the same selection and decisions as the measured
calibrated learner.
-/

open Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m J : ℕ}

private lemma clockAnnotations_id {P : Type*} (π : Policy P n) :
    π.withClockAnnotations id = π := by
  have hh (H : History n) : annotateClockHistory id H = H := by
    funext i
    cases h : H i <;> simp [annotateClockHistory,h]
  cases π
  simp only [Policy.withClockAnnotations, id_eq, hh]

private lemma terminalClockReport_id : terminalClockReport id = id := by
  funext t
  by_cases h : t=1 <;> simp [terminalClockReport,h]

private lemma sortedArithmeticDuration_eq {P : Type} [NeZero m] (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m P) (q : Reservoir n m) (x u : Fin n → ℝ)
    (r : PolicyQueryArray n J P) (j : Fin (J+1))
    (hu : Function.Injective u) (huUnit : ∀ i, u i∈Ico (0 : ℝ) 1) :
    let p := (countedArrivalOrder u).1
    let s := u ∘ p
    (frozenFamilyPolicy zlo zhi estimate q j).clockToRank.reportedDuration (s,r) p x s =
      validationDuration zlo zhi estimate q (x,u,r) j := by
  dsimp only
  let p := (countedArrivalOrder u).1
  let s := u ∘ p
  let π := frozenFamilyPolicy zlo zhi estimate q j
  have hs : StrictMono s := (countedArrivalOrder_monotone u).strictMono_of_injective (hu.comp p.injective)
  have hs1 (k : Fin n) : s k<1 := (huUnit _).2
  have hRecon : Instance.reconstructClocks (s,p)=u := by
    funext i
    change u (p (p.symm i))=u i
    rw [p.apply_symm_apply]
  have hRamp : (fun i => unitRamp (u i)) = u :=
    funext (fun i => unitRamp_eq ⟨(huUnit i).1,(huUnit i).2.le⟩)
  have h := π.withClockAnnotations_report_eq_rank id r s hs hs1 p x
  rw [clockAnnotations_id, terminalClockReport_id, id_eq, hRecon, Function.id_comp] at h
  unfold validationDuration
  rw [hRamp]
  exact h.symm

/-- Agreement on the actual validation clock profiles and every online
history. Neither the current decision nor this comparison reads future
online offers. -/
theorem countedArithmeticDecision_eq_measured [NeZero m]
    (targetScale thresholdScale : ArithmeticCalibrationScale)
    (mu zlo zhi : ℝ) (q : Reservoir n m) (x clocks : Fin m → Fin n → ℝ)
    (banks : CalibrationQueryArrays n m J (ArithmeticCalibrationBank n m targetScale)
      (ArithmeticCalibrationBank n m thresholdScale))
    (hClocks : ∀ a, Function.Injective (clocks a))
    (hUnit : ∀ a i, clocks a i∈Ico (0 : ℝ) 1) (coin t offer : ℝ) (H : History n) (i : Fin n) :
    let target := calibrationTargetCall (n := n) (m := m) targetScale.accuracy targetScale.failure targetScale.failure_mem
    let estimate := calibrationPlannerCall (n := n) (m := m) thresholdScale.accuracy thresholdScale.failure thresholdScale.failure_mem
    let rho := computedTarget mu target (reservoirCoordinates q) banks.1
    let worlds := fun a => (x a,clocks a,banks.2.1 a)
    let point := (q,validationSelection zlo zhi estimate q worlds rho)
    (countedArithmeticDecision thresholdScale
      (countedArithmeticPrepare targetScale thresholdScale mu zlo zhi q x clocks banks coin)
      t offer H i banks.2.2).1 =
      decidePrepared zlo zhi estimate point banks.2.2 coin t i offer H := by
  dsimp only
  let target := calibrationTargetCall (n := n) (m := m) targetScale.accuracy targetScale.failure targetScale.failure_mem
  let estimate := calibrationPlannerCall (n := n) (m := m) thresholdScale.accuracy thresholdScale.failure thresholdScale.failure_mem
  let targetWork := fun z s => (countedArithmeticCalibrationCall targetScale q Finset.univ 1 z s).2
  let policyWork := fun A u z s => (countedArithmeticCalibrationCall thresholdScale q A u z s).2
  let profile := (countedArithmeticValidationProfiles x clocks banks.2.1).1
  let worlds := fun a => (x a,clocks a,banks.2.1 a)
  let tau := fun a => validationDuration zlo zhi estimate q (worlds a)
  have hT : (fun z => countedArithmeticCalibrationCall targetScale q Finset.univ 1 z) =
      fun z s => (target q z s,targetWork z s) := by
    funext z s
    exact Prod.ext (countedArithmeticCalibrationCall_value targetScale q Finset.univ 1 z s) rfl
  have hP : countedArithmeticCalibrationCall thresholdScale q =
      fun A u z s => (estimate q A u z s,policyWork A u z s) := by
    funext A u z s
    exact Prod.ext (countedArithmeticCalibrationCall_value thresholdScale q A u z s) rfl
  have hDuration (a : Fin m) (j : Fin (J+1)) :
      let p := profile a
      let out := countedRankValidationMemo (familyCoefficient zlo zhi J)
        (fun A u z s => (estimate q A u z s,policyWork A u z s))
        q (decide (familyFallback q)) p.1 p.2.1 p.2.2.1 p.2.2.2
      (out.1[j.val]?).getD 1=tau a j := by
    dsimp only
    have hp : profile a =
        ((countedArrivalOrder (clocks a)).1,x a,
          (fun k => clocks a ((countedArrivalOrder (clocks a)).1 k)),banks.2.1 a) := by
      simp [profile,countedArithmeticValidationProfiles,Vector.get]
    rw [hp]
    let p := (countedArrivalOrder (clocks a)).1
    let s := clocks a ∘ p
    let out := countedRankValidationMemo (familyCoefficient zlo zhi J)
      (fun A u z s => (estimate q A u z s,policyWork A u z s))
      q (decide (familyFallback q)) p (x a) s (banks.2.1 a)
    change (out.1[j.val]?).getD 1=tau a j
    have hsize : out.1.size=J+1 := countedRankValidationMemo_size _ _ _ _ _ _ _ _
    have hj : j.val<out.1.size := hsize.symm ▸ j.isLt
    rw [Array.getElem?_eq_getElem hj,Option.getD_some]
    exact (countedRankValidationMemo_eq_reportedDuration zlo zhi estimate policyWork q p (x a) s
      (banks.2.1 a) j).trans
        (sortedArithmeticDuration_eq zlo zhi estimate q (x a) (clocks a) (banks.2.1 a) j
          (hClocks a) (hUnit a))
  have hPrep := countedCalibrationPrepare_selection mu zlo zhi target targetWork estimate policyWork
    q banks.1 profile tau hDuration
  dsimp only at hPrep
  unfold countedArithmeticDecision countedArithmeticPrepare
  dsimp only
  rw [hT,hP,storedCalibrationCoefficient_value,hPrep.2.1,hPrep.2.2]
  exact countedOnlineCalibrationDecision_eq zlo zhi estimate policyWork q banks.2.2 _ t offer H i

end ProphetSecretary.Statistics.Calibration
