import ProphetSecretary.Statistics.CalibratedLearner
import ProphetSecretary.Statistics.CalibratedValidationMemo
import ProphetSecretary.Statistics.EmpiricalMaximumWork

/-!
# One preparation for the calibrated learner

The empirical maximum and count are computed once, as are each validation
profile's durations. Knot means are stored before the first crossing scan.
The policy then retains the selected point and the empirical fallback flag.
-/

open ProphetSecretary.Model
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration

variable {n m J : ℕ} {TSeed PSeed : Type}

private lemma le_foldl_min_iff {a b : ℝ} (l : List ℝ) :
    b≤l.foldl min a ↔ b≤a ∧ ∀ x ∈ l,b≤x := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons,ih,le_min_iff,List.mem_cons]
    aesop

noncomputable def memoTarget [NeZero m] (mu L M : ℝ) (estimate : TargetEstimator n m TSeed)
    (q : Reservoir n m) (r : TargetGrid m → TSeed) : ℝ :=
  if L≤targetCountCutoff m ∧ mu/2≤M then
    let ratios := List.ofFn (fun j : TargetGrid m =>
      (estimate q (targetGrid j) (r j)+1/(m : ℝ))/(M+targetGrid j))
    max (1/2) (ratios.foldl min (4/5))
  else 4/5

lemma memoTarget_eq [NeZero m] (mu : ℝ) (estimate : TargetEstimator n m TSeed)
    (q : Reservoir n m) (r : TargetGrid m → TSeed) :
    memoTarget mu (empiricalPositiveCount (reservoirCoordinates q))
      (trainingExpectedMaximum (reservoirCoordinates q)) estimate q r =
      computedTarget mu estimate (reservoirCoordinates q) r := by
  let a := reservoirCoordinates q
  change memoTarget mu (empiricalPositiveCount a) (trainingExpectedMaximum a) estimate q r=
    computedTarget mu estimate a r
  by_cases he : targetEligible mu a
  · have hg : ¬ (targetCountCutoff m < empiricalPositiveCount a ∨ trainingExpectedMaximum a < mu/2) :=
      not_or_intro (not_lt_of_ge he.1) (not_lt_of_ge he.2)
    have hq : reservoirCoordinates.symm a = q := reservoirCoordinates.symm_apply_apply q
    have he' : empiricalPositiveCount a≤targetCountCutoff m ∧ mu/2≤trainingExpectedMaximum a := he
    rw [memoTarget,if_pos he',computedTarget,if_pos he,numericalTarget,if_neg hg]
    have hv : targetTable mu estimate a r = fun j => estimate q (targetGrid j) (r j) := by
      funext j
      rw [targetTable,if_pos he,hq]
    rw [hv]
    let v := fun j : TargetGrid m => (estimate q (targetGrid j) (r j)+1/(m : ℝ))/
      (trainingExpectedMaximum a+targetGrid j)
    let L := List.ofFn v
    have h : L.foldl min (4/5)=min (4/5) (targetMinimumRatio a (fun j => estimate q (targetGrid j) (r j))) := by
      apply eq_of_forall_le_iff
      intro z
      rw [le_foldl_min_iff,le_min_iff]
      simp only [targetMinimumRatio,Finset.le_inf'_iff,Finset.mem_univ,true_implies]
      exact ⟨fun hz => ⟨hz.1,fun j => hz.2 (v j) (List.mem_ofFn.mpr ⟨j,rfl⟩)⟩,fun hz =>
        ⟨hz.1,fun x hx => by
          obtain ⟨j,rfl⟩ := List.mem_ofFn.mp (show x∈List.ofFn v from hx)
          exact hz.2 j⟩⟩
    change max (1/2) (L.foldl min (4/5)) =
      min (4/5) (max (1/2) (targetMinimumRatio a (fun j => estimate q (targetGrid j) (r j))))
    rw [h,max_min_distrib_left,max_eq_right (by norm_num : (1/2 : ℝ) ≤ 4/5)]
  · have he' : ¬ (empiricalPositiveCount a≤targetCountCutoff m ∧ mu/2≤trainingExpectedMaximum a) := he
    rw [memoTarget,if_neg he',computedTarget,if_neg he]

noncomputable def memoValidationKnots (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) (fallback : Bool) :
    Array ℝ :=
  let durations := Array.ofFn (fun a => memoValidationDurationsWithGuard zlo zhi estimate q (w a) fallback)
  Array.ofFn (fun k : Fin (J+3) => (m : ℝ)⁻¹*
    ∑ a : Fin m, durationKnots (fun j : Fin (J+1) => ((durations[a.val]?.getD #[])[j.val]?).getD 1) k.val)

@[simp] lemma memoValidationKnots_size (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) (fallback : Bool) :
    (memoValidationKnots zlo zhi estimate q w fallback).size=J+3 := by simp [memoValidationKnots]

lemma memoValidationKnots_eq [NeZero m] (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) (k : ℕ) :
    ((memoValidationKnots zlo zhi estimate q w (decide (familyFallback q)))[k]?).getD 1 =
      meanDurationKnots zlo zhi estimate q w k := by
  by_cases hk : k < J+3
  · have hK : k < (memoValidationKnots zlo zhi estimate q w (decide (familyFallback q))).size := by
      simpa only [memoValidationKnots_size] using hk
    rw [Array.getElem?_eq_getElem hK,Option.getD_some]
    simp only [memoValidationKnots,Array.getElem_ofFn,meanDurationKnots]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    funext j
    simp only [Array.getElem?_ofFn, a.isLt, dite_true, Option.getD_some]
    have hJ : j.val < (memoValidationDurations zlo zhi estimate q (w a)).size := by
      simpa only [memoValidationDurations_size] using j.isLt
    change ((memoValidationDurations zlo zhi estimate q (w a))[j.val]?).getD 1=_
    rw [Array.getElem?_eq_getElem hJ,Option.getD_some,memoValidationDurations_eq]
  · have hK : ¬ k < (memoValidationKnots zlo zhi estimate q w (decide (familyFallback q))).size := by
      simpa only [memoValidationKnots_size] using hk
    rw [Array.getElem?_eq_none (Nat.le_of_not_lt hK)]
    simp only [Option.getD_none,meanDurationKnots,durationKnots,if_neg (show k≠0 by omega),
      dif_neg (show ¬ k≤J+1 by omega),Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,mul_one]
    exact (inv_mul_cancel₀ (by exact_mod_cast NeZero.ne m)).symm

noncomputable def memoValidationSelection (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) (fallback : Bool) (ρ : ℝ) :
    ℕ × ℝ :=
  let A := memoValidationKnots zlo zhi estimate q w fallback
  let v := fun k => (A[k]?).getD 1
  let k := calibrationCrossing v ρ (J+2)
  (k,(ρ-v (k-1))/(v k-v (k-1)))

lemma memoValidationSelection_eq [NeZero m] (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (w : Fin m → World n (PolicyQueryArray n J PSeed)) (ρ : ℝ) :
    memoValidationSelection zlo zhi estimate q w (decide (familyFallback q)) ρ =
      validationSelection zlo zhi estimate q w ρ := by
  simp only [memoValidationSelection,validationSelection,calibrationMixingFraction,memoValidationKnots_eq]

abbrev MemoPreparedCalibration (n m : ℕ) := PreparedCalibration n m × Bool

noncomputable def prepareMemo [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) : MemoPreparedCalibration n m :=
  let d := calibratedExperiment p
  let a := d.1.1
  let q := reservoirCoordinates.symm a
  let L := empiricalPositiveCount a
  let M := (countedEmpiricalMaximum (empiricalStoredRows (fun i j => a (i,j)))).1
  let fallback := decide (targetCountCutoff m<L ∨ 1/4<M)
  let ρ := memoTarget mu L M targetEstimate q d.1.2
  ((q,memoValidationSelection zlo zhi policyEstimate q d.2.1 fallback ρ),fallback)

lemma prepareMemo_eq [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed) :
    prepareMemo mu zlo zhi targetEstimate policyEstimate p =
      (prepare mu zlo zhi targetEstimate policyEstimate p,
        decide (familyFallback (prepare mu zlo zhi targetEstimate policyEstimate p).1)) := by
  let d := calibratedExperiment p
  let q := reservoirCoordinates.symm d.1.1
  have hQ : reservoirCoordinates q=d.1.1 := reservoirCoordinates.apply_symm_apply _
  have hM : (countedEmpiricalMaximum (empiricalStoredRows (fun i j => d.1.1 (i,j)))).1 =
      trainingExpectedMaximum d.1.1 := countedEmpiricalMaximum_eq_legacy _
  have hFallback : decide (targetCountCutoff m<empiricalPositiveCount d.1.1 ∨
      1/4<trainingExpectedMaximum d.1.1)=decide (familyFallback q) := by
    unfold familyFallback
    rw [hQ]
    apply Bool.eq_iff_iff.mpr
    simp only [decide_eq_true_eq]
    rfl
  have hρ := memoTarget_eq mu targetEstimate q d.1.2
  rw [hQ] at hρ
  change ((q,memoValidationSelection zlo zhi policyEstimate q d.2.1
      (decide (targetCountCutoff m<empiricalPositiveCount d.1.1 ∨
        1/4<(countedEmpiricalMaximum (empiricalStoredRows (fun i j => d.1.1 (i,j)))).1))
      (memoTarget mu (empiricalPositiveCount d.1.1)
        (countedEmpiricalMaximum (empiricalStoredRows (fun i j => d.1.1 (i,j)))).1 targetEstimate q d.1.2)),
      decide (targetCountCutoff m<empiricalPositiveCount d.1.1 ∨
        1/4<(countedEmpiricalMaximum (empiricalStoredRows (fun i j => d.1.1 (i,j)))).1)) =
    ((q,validationSelection zlo zhi policyEstimate q d.2.1 (computedTarget mu targetEstimate d.1.1 d.1.2)),
      decide (familyFallback q))
  rw [hM,hFallback,hρ,memoValidationSelection_eq]

/-- Execution needs only the prepared data, current observation and fresh seeds. -/
noncomputable def decidePreparedMemo (zlo zhi : ℝ) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : MemoPreparedCalibration n m) (r : PolicyQueryArray n J PSeed) (coin t : ℝ)
    (i : Fin n) (x : ℝ) (H : History n) : Bool :=
  if p.2 then decide (x=1)
  else (cappedHistoryThresholdPolicy (familyThreshold zlo zhi policyEstimate
    (mixturePolicyIndex J p.1.2 coin))).decide (p.1.1,r) t i x H

lemma decidePreparedMemo_eq [NeZero m] (zlo zhi : ℝ) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : PreparedCalibration n m) (r : PolicyQueryArray n J PSeed) (coin t : ℝ)
    (i : Fin n) (x : ℝ) (H : History n) :
    decidePreparedMemo zlo zhi policyEstimate (p,decide (familyFallback p.1)) r coin t i x H =
      decidePrepared zlo zhi policyEstimate p r coin t i x H := by
  simp only [decidePreparedMemo,decidePrepared,numericalFamilyPolicy,decide_eq_true_eq]

/-- One prepared execution gives the mathematical policy on every raw input. -/
lemma memoExecution_eq_samplePolicy [NeZero m] (mu zlo zhi : ℝ)
    (targetEstimate : TargetEstimator n m TSeed) (policyEstimate : ContinuationEstimator n m PSeed)
    (p : Reservoir n (2*m) × CalibratedSeed n m J TSeed PSeed)
    (t : ℝ) (i : Fin n) (x : ℝ) (H : History n) :
    decidePreparedMemo zlo zhi policyEstimate (prepareMemo mu zlo zhi targetEstimate policyEstimate p)
        p.2.2.2.1 p.2.2.2.2 t i x H =
      (samplePolicy mu zlo zhi targetEstimate policyEstimate).decide p t i x H := by
  rw [prepareMemo_eq,decidePreparedMemo_eq]
  rfl

/-- The target grid and all validation and online continuation slots. -/
def calibratedQuerySlots (n m J : ℕ) : ℕ := (4*m+1)+(m+1)*(n*(J+1))

lemma calibratedQuerySlots_le (n m J : ℕ) (hJ : J≤m) :
    calibratedQuerySlots n m J≤(n+5)*(m+1)^2 := by
  have hFirst : 4*m+1≤5*(m+1)^2 := by nlinarith
  have hLater := Nat.mul_le_mul_left (m+1) (Nat.mul_le_mul_left n (Nat.succ_le_succ hJ))
  unfold calibratedQuerySlots
  calc
    _ ≤ 5*(m+1)^2+(m+1)*(n*(m+1)) := Nat.add_le_add hFirst hLater
    _ = _ := by ring

end ProphetSecretary.Statistics.Calibration
