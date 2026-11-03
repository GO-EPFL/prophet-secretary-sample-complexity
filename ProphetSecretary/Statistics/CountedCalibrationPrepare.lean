import ProphetSecretary.Statistics.CalibratedPreparationMemo
import ProphetSecretary.Statistics.RankValidationMemo
import ProphetSecretary.Statistics.CalibratedQueryExecution

/-!
# Counted preparation of the bounded policy

The empirical maximum, count guard, target queries, validation profiles and
first crossing are each evaluated once. The result stores the empirical
rows, the selected segment and mixing fraction, and the fallback decision.
-/

open MeasureTheory Set
open scoped Classical BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed K : Type} [Field K] [LinearOrder K]

def countedTargetMinimum (mu L M Lbar : K) (estimate : K → TSeed → K × ℕ)
    (r : TargetGrid m → TSeed) : K × ℕ :=
  if L≤Lbar ∧ mu/2≤M then
    let vals := List.ofFn fun j : TargetGrid m =>
      let z := (j.val : K)/(m : K)
      let q := estimate z (r j)
      ((q.1+1/(m : K))/(M+z),q.2+8)
    let res := vals.foldl (fun s q => (min s.1 q.1,s.2+q.2+2)) (4/5,6)
    (max (1/2) res.1,res.2+2)
  else (4/5,5)

omit [Field K] in
private lemma targetFold_work_le (l : List (K × ℕ)) (W : ℕ) (q : K × ℕ)
    (hW : ∀ x∈l, x.2≤W) :
    (l.foldl (fun s x => (min s.1 x.1,s.2+x.2+2)) q).2≤q.2+l.length*(W+2) := by
  induction l generalizing q with
  | nil => simp
  | cons a l ih =>
    simp only [List.foldl_cons,List.length_cons]
    have h := ih (min q.1 a.1,q.2+a.2+2) (fun b hb => hW b (List.mem_cons_of_mem _ hb))
    exact h.trans (by have ha := hW a (List.mem_cons_self); nlinarith only [ha])

lemma countedTargetMinimum_work (mu L M Lbar : K) (estimate : K → TSeed → K × ℕ)
    (r : TargetGrid m → TSeed) (W : ℕ) (hW : ∀ z s, (estimate z s).2≤W) :
    (countedTargetMinimum mu L M Lbar estimate r).2≤(4*m+1)*(W+10)+8 := by
  unfold countedTargetMinimum
  split_ifs
  · let f := fun j : TargetGrid m =>
      let z := (j.val : K)/(m : K)
      let q := estimate z (r j)
      ((q.1+1/(m : K))/(M+z),q.2+8)
    have hF (x : K × ℕ) (hx : x∈List.ofFn f) : x.2≤W+8 := by
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx
      exact Nat.add_le_add_right (hW _ _) 8
    have hh := targetFold_work_le (List.ofFn f) (W+8) (4/5,6) hF
    simp only [List.length_ofFn, show W+8+2=W+10 by omega] at hh
    change ((List.ofFn f).foldl (fun s q => (min s.1 q.1,s.2+q.2+2)) (4/5,6)).2+2≤_
    omega
  · change 5≤(4*m+1)*(W+10)+8
    omega

omit [Field K] in
private lemma targetFold_value (l : List (K × ℕ)) (q : K × ℕ) :
    (l.foldl (fun s x => (min s.1 x.1,s.2+x.2+2)) q).1=(l.map Prod.fst).foldl min q.1 := by
  induction l generalizing q with
  | nil => rfl
  | cons a l ih => simpa only [List.foldl_cons,List.map_cons] using ih (min q.1 a.1,q.2+a.2+2)

lemma countedTargetMinimum_value [NeZero m] (mu L M : ℝ)
    (estimate : TargetEstimator n m TSeed) (cost : ℝ → TSeed → ℕ)
    (q : Reservoir n m) (r : TargetGrid m → TSeed) :
    (countedTargetMinimum mu L M (targetCountCutoff m)
      (fun z s => (estimate q z s,cost z s)) r).1 = memoTarget mu L M estimate q r := by
  unfold countedTargetMinimum memoTarget
  split_ifs
  · dsimp only
    rw [targetFold_value,List.map_ofFn]
    rfl
  · rfl

def countedKnotScan (v : ℕ → K) (rho : K) (j : ℕ) : ℕ → ℕ × ℕ
  | 0 => (j,1)
  | k+1 => if rho≤v (j+1) then (j+1,4)
    else let q := countedKnotScan v rho (j+1) k; (q.1,q.2+4)

omit [Field K] in
lemma countedKnotScan_work (v : ℕ → K) (rho : K) (j k : ℕ) :
    (countedKnotScan v rho j k).2≤4*k+1 := by
  induction k generalizing j with
  | zero => simp [countedKnotScan]
  | succ k ih =>
    rw [countedKnotScan]
    have h := ih (j+1)
    split_ifs <;> dsimp only <;> omega

lemma countedKnotScan_value [IsStrictOrderedRing K] (v : ℕ → K) (rho : K) (j k : ℕ) :
    (countedKnotScan v rho j k).1=j+calibrationCrossing (fun a => v (j+a)) rho k := by
  induction k generalizing j with
  | zero => simp [countedKnotScan,calibrationCrossing]
  | succ k ih =>
    rw [countedKnotScan,calibrationCrossing]
    split_ifs
    · rfl
    · dsimp only
      rw [ih]
      rw [show (fun a => v (j+1+a))=(fun a => v (j+(a+1))) by funext a; congr 1; omega]
      omega

def countedCalibrationGridSize (m : ℕ) (zlo zhi : K) : ℕ × ℕ :=
  let q := countedKnotScan (fun j : ℕ => (j : K)) ((m : K)*(zhi-zlo)) 0 m
  (q.1,q.2+4)

lemma countedCalibrationGridSize_work (m : ℕ) (zlo zhi : K) :
    (countedCalibrationGridSize m zlo zhi).2≤4*m+5 := by
  have h := countedKnotScan_work (fun j : ℕ => (j : K)) ((m : K)*(zhi-zlo)) 0 m
  exact Nat.add_le_add_right h 4

lemma countedCalibrationGridSize_value {m : ℕ} (hm : 0<m) {zlo zhi : ℝ}
    (hlo : zlo<zhi) (hhi : zhi-zlo≤1) :
    (countedCalibrationGridSize m zlo zhi).1=familyGridSize m zlo zhi := by
  unfold countedCalibrationGridSize
  dsimp only
  rw [countedKnotScan_value]
  simp only [Nat.zero_add]
  let rho := (m : ℝ)*(zhi-zlo)
  have hp : 0<rho := mul_pos (by exact_mod_cast hm) (sub_pos.mpr hlo)
  have hq : rho≤m := mul_le_of_le_one_right (by positivity) hhi
  have h := calibrationCrossing_bounds (fun j : ℕ => (j : ℝ)) rho m (by simpa using hp) hq
  exact ((Nat.ceil_eq_iff (by omega : calibrationCrossing (fun j : ℕ => (j : ℝ)) rho m ≠ 0)).mpr
    ⟨h.2.2.1,h.2.2.2⟩).symm

abbrev CalibrationRankProfile (n J : ℕ) (K PSeed : Type) :=
  Equiv.Perm (Fin n) × ((Fin n → K) × ((Fin n → K) × PolicyQueryArray n J PSeed))

def countedCalibrationKnots (duration : Fin m → Array K) (J : ℕ) : Array K :=
  Array.ofFn (fun k : Fin (J+3) =>
    if k.val=0 then 0 else if k.val≤J+1 then
      (m : K)⁻¹ * ∑ r : Fin m, ((duration r)[k.val-1]?).getD 1
    else 1)

lemma countedCalibrationKnots_value [NeZero m] (duration : Fin m → Array ℝ) (J k : ℕ) :
    ((countedCalibrationKnots duration J)[k]?).getD 1 =
      (m : ℝ)⁻¹ * ∑ r : Fin m, durationKnots
        (fun j : Fin (J+1) => ((duration r)[j.val]?).getD 1) k := by
  by_cases h : k<J+3
  · simp only [countedCalibrationKnots,Array.getElem?_ofFn,h,dite_true,Option.getD_some,durationKnots]
    split_ifs <;> simp_all [Finset.sum_const, Fintype.card_fin,
      inv_mul_cancel₀ (by exact_mod_cast NeZero.ne m : (m : ℝ)≠0)]
  · have hk : ¬k≤J+1 := by omega
    have h0 : k≠0 := by omega
    simp [countedCalibrationKnots,h,durationKnots,h0,hk,
      inv_mul_cancel₀ (by exact_mod_cast NeZero.ne m : (m : ℝ)≠0)]

structure CountedCalibrationPreparation (K : Type) (n m : ℕ) where
  rows : Fin n → Fin m → K
  selection : ℕ × K
  fallback : Bool
  work : ℕ

private lemma vector_get_ofFn {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

def storedCalibrationCoefficient (J : ℕ) (zlo zhi : K) : ℕ → K :=
  let a : Vector K (J+1) := Vector.ofFn fun j => zlo+(j.val : K)/(J : K)*(zhi-zlo)
  fun k => a.get (coefficientIndex J k)

lemma storedCalibrationCoefficient_value (J : ℕ) (zlo zhi : ℝ) :
    storedCalibrationCoefficient J zlo zhi=familyCoefficient zlo zhi J := by
  funext k
  simp only [storedCalibrationCoefficient,vector_get_ofFn,coefficientIndex,familyCoefficient]

def countedCalibrationPrepare (mu zlo zhi Lbar : K)
    (target : K → TSeed → K × ℕ)
    (estimate : Finset (Fin n) → K → K → PSeed → K × ℕ)
    (q : Fin n → Fin m → K) (r : TargetGrid m → TSeed)
    (profile : Fin m → CalibrationRankProfile n J K PSeed) :
    CountedCalibrationPreparation K n m :=
  let M := countedEmpiricalMaximum (empiricalStoredRows q)
  let p := countedPlannerProbabilities (plannerStoredRows q)
  let L := ∑ i : Fin n, plannerProbabilityRead p.1 i
  let fallback := decide (Lbar<L ∨ 1/4<M.1)
  let rho := countedTargetMinimum mu L M.1 Lbar target r
  let z := storedCalibrationCoefficient J zlo zhi
  let results : Vector (Array K × ℕ) m := Vector.ofFn fun r =>
    let v := profile r
    countedRankValidationMemo z estimate q fallback v.1 v.2.1 v.2.2.1 v.2.2.2
  let A := countedCalibrationKnots (fun r => (results.get r).1) J
  let v := fun k => (A[k]?).getD 1
  let k := countedKnotScan v rho.1 0 (J+2)
  let alpha := (rho.1-v (k.1-1))/(v k.1-v (k.1-1))
  ⟨q,(k.1,alpha),fallback,
    M.2+p.2+rho.2+(∑ r : Fin m, ((results.get r).2+6))+
      6*(n+1)*(m+1)+10*(m+1)*(J+3)+8*(J+1)+k.2+14⟩

theorem countedCalibrationPrepare_work (mu zlo zhi Lbar : K)
    (target : K → TSeed → K × ℕ)
    (estimate : Finset (Fin n) → K → K → PSeed → K × ℕ)
    (q : Fin n → Fin m → K) (r : TargetGrid m → TSeed)
    (profile : Fin m → CalibrationRankProfile n J K PSeed) (WT WP : ℕ)
    (hT : ∀ z s, (target z s).2≤WT) (hP : ∀ A u z s, (estimate A u z s).2≤WP) :
    (countedCalibrationPrepare mu zlo zhi Lbar target estimate q r profile).work≤
      100*(n+1)^2*(m+1)^2+26*(n+1)*(m+1)+(4*m+1)*(WT+10)+8+
      m*(n*(n*(m+2)+7+(J+1)*(WP+2))+(J+1)*(12*n+3)+6)+
      10*(m+1)*(J+3)+8*(J+1)+4*(J+2)+15 := by
  unfold countedCalibrationPrepare
  dsimp only
  have hM := countedEmpiricalMaximum_work_le_rows q (fun _ => le_rfl)
  have hp := countedPlannerProbabilities_work (plannerStoredRows q) m (fun _ => by simp)
  have ht := countedTargetMinimum_work mu
    (∑ i : Fin n, plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows q)).1 i)
    (countedEmpiricalMaximum (empiricalStoredRows q)).1 Lbar target r WT hT
  simp only [vector_get_ofFn]
  have hV : ∀ (r : Fin m) (z : ℕ → K) (fallback : Bool),
      let v := profile r
      (countedRankValidationMemo z estimate q fallback v.1 v.2.1 v.2.2.1 v.2.2.2).2+6 ≤
        n*(n*(m+2)+7+(J+1)*(WP+2))+(J+1)*(12*n+3)+6 := fun r z b =>
      Nat.add_le_add_right (countedRankValidationMemo_work_le z estimate q b
        (profile r).1 (profile r).2.1 (profile r).2.2.1 (profile r).2.2.2 WP hP) 6
  have hsV (z : ℕ → K) (fallback : Bool) :
      (∑ r : Fin m, ((countedRankValidationMemo z estimate q fallback (profile r).1
        (profile r).2.1 (profile r).2.2.1 (profile r).2.2.2).2+6)) ≤
        m*(n*(n*(m+2)+7+(J+1)*(WP+2))+(J+1)*(12*n+3)+6) :=
    (Finset.sum_le_sum (fun r _ => hV r z fallback)).trans_eq (by simp)
  have h26 : 26*(n+1)*(m+1)=20*(n+1)*(m+1)+6*(n+1)*(m+1) := by ring
  rw [h26]
  let z := storedCalibrationCoefficient J zlo zhi
  let L := ∑ i : Fin n, plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows q)).1 i
  let M := (countedEmpiricalMaximum (empiricalStoredRows q)).1
  let b := decide (Lbar<L ∨ 1/4<M)
  let duration (r : Fin m) := (countedRankValidationMemo z estimate q b (profile r).1
    (profile r).2.1 (profile r).2.2.1 (profile r).2.2.2).1
  let v := fun k : ℕ => ((countedCalibrationKnots duration J)[k]?).getD 1
  let rho := (countedTargetMinimum mu L M Lbar target r).1
  have hScan := countedKnotScan_work v rho 0 (J+2)
  have hVal := hsV z b
  dsimp only [v,duration,z,b,rho,L,M] at hScan
  dsimp only [z,b,L,M] at hVal
  omega

private lemma countedCalibrationPositiveCount_value (q : Reservoir n m) :
    (∑ i : Fin n, plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows q)).1 i) =
      empiricalPositiveCount (reservoirCoordinates q) := by
  simp_rw [countedPlannerProbabilities_ofFn, empiricalPositiveProbability, positiveObservations]
  unfold empiricalPositiveCount
  rw [Fintype.sum_prod_type, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [div_eq_mul_inv, mul_comm, ← Finset.sum_boole]
  rfl

/-- The returned point is the first crossing of the mean of the actual
per-profile duration curves. The correspondence applies to continuous or
grid timestamps once the profile execution is identified. -/
theorem countedCalibrationPrepare_selection [NeZero m] (mu zlo zhi : ℝ)
    (target : TargetEstimator n m TSeed) (targetWork : ℝ → TSeed → ℕ)
    (estimate : ContinuationEstimator n m PSeed)
    (estimateWork : Finset (Fin n) → ℝ → ℝ → PSeed → ℕ)
    (q : Reservoir n m) (r : TargetGrid m → TSeed)
    (profile : Fin m → CalibrationRankProfile n J ℝ PSeed)
    (τ : Fin m → Fin (J+1) → ℝ)
    (hDuration : ∀ (a : Fin m) (j : Fin (J+1)),
      let p := profile a
      let out := countedRankValidationMemo (familyCoefficient zlo zhi J)
        (fun A u z s => (estimate q A u z s,estimateWork A u z s))
        q (decide (familyFallback q)) p.1 p.2.1 p.2.2.1 p.2.2.2
      (out.1[j.val]?).getD 1=τ a j) :
    let out := countedCalibrationPrepare mu zlo zhi (targetCountCutoff m)
      (fun z s => (target q z s,targetWork z s))
      (fun A u z s => (estimate q A u z s,estimateWork A u z s)) q r profile
    let rho := computedTarget mu target (reservoirCoordinates q) r
    let v := fun k => (m : ℝ)⁻¹*∑ a : Fin m, durationKnots (τ a) k
    out.rows=q ∧ out.fallback=decide (familyFallback q) ∧
      out.selection=(calibrationCrossing v rho (J+2),calibrationMixingFraction v rho (J+2)) := by
  dsimp only
  have hM : (countedEmpiricalMaximum (empiricalStoredRows q)).1 =
      trainingExpectedMaximum (reservoirCoordinates q) := by
    exact countedEmpiricalMaximum_eq_legacy (reservoirCoordinates q)
  unfold countedCalibrationPrepare
  dsimp only
  rw [countedCalibrationPositiveCount_value,hM]
  rw [show decide (targetCountCutoff m<empiricalPositiveCount (reservoirCoordinates q) ∨
    1/4<trainingExpectedMaximum (reservoirCoordinates q)) = decide (familyFallback q) by
      apply Bool.eq_iff_iff.mpr
      simp only [decide_eq_true_eq]
      unfold familyFallback trainingExpectedMaximum trainingInstance
      rw [MeasurableEquiv.symm_apply_apply]]
  rw [countedTargetMinimum_value, memoTarget_eq]
  simp only [vector_get_ofFn, storedCalibrationCoefficient_value]
  let duration := fun a : Fin m =>
    let p := profile a
    (countedRankValidationMemo (familyCoefficient zlo zhi J)
      (fun A u z s => (estimate q A u z s,estimateWork A u z s))
      q (decide (familyFallback q)) p.1 p.2.1 p.2.2.1 p.2.2.2).1
  let V := fun k : ℕ => ((countedCalibrationKnots duration J)[k]?).getD 1
  let v := fun k => (m : ℝ)⁻¹*∑ a : Fin m, durationKnots (τ a) k
  let rho := computedTarget mu target (reservoirCoordinates q) r
  have hv : V=v := by
    funext k
    rw [show V k = _ from countedCalibrationKnots_value duration J k]
    simp only [v]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    funext j
    exact hDuration a j
  refine ⟨by trivial,by trivial,?_⟩
  change ((countedKnotScan V rho 0 (J+2)).1,
      (rho-V ((countedKnotScan V rho 0 (J+2)).1-1))/
        (V (countedKnotScan V rho 0 (J+2)).1-V ((countedKnotScan V rho 0 (J+2)).1-1))) =
    (calibrationCrossing v rho (J+2),calibrationMixingFraction v rho (J+2))
  rw [hv,countedKnotScan_value]
  simp [calibrationMixingFraction]

end ProphetSecretary.Statistics.Calibration
