import ProphetSecretary.Statistics.RationalCalibrationLoops
import ProphetSecretary.Statistics.CountedCalibrationPrepare
import ProphetSecretary.Statistics.ReportedRankPreparation
import ProphetSecretary.Statistics.ScalarPlannerRational
import Mathlib.Data.Rat.BigOperators

/-!
# Rational preparation realizes the same interpolation

The empirical maximum, positive count, target minimum, recorded duration
knots, and first-crossing index all commute with casting rational values.
Only numerical outputs are compared: work is counted on the rational
program itself.
-/

open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m J : ℕ} {TSeed PSeed : Type}

private lemma castFoldMin (l : List ℚ) (a : ℚ) :
    ((l.foldl min a : ℚ) : ℝ)=(l.map (fun x : ℚ => (x : ℝ))).foldl min (a : ℝ) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons,List.map_cons,ih,Rat.cast_min]

private lemma foldCountedMinValue {K : Type*} [Min K] (l : List (K × ℕ)) (a : K × ℕ) :
    (l.foldl (fun s x => (min s.1 x.1,s.2+x.2+2)) a).1=(l.map Prod.fst).foldl min a.1 := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact ih (min a.1 b.1,a.2+b.2+2)

lemma countedTargetMinimum_ratCast (mu L M Lbar : ℚ)
    (target : ℚ → TSeed → ℚ × ℕ) (targetR : ℝ → TSeed → ℝ × ℕ)
    (ht : ∀ z s, ((target z s).1 : ℝ)=(targetR (z : ℝ) s).1)
    (r : TargetGrid m → TSeed) :
    ((countedTargetMinimum mu L M Lbar target r).1 : ℝ) =
      (countedTargetMinimum (mu : ℝ) (L : ℝ) (M : ℝ) (Lbar : ℝ) targetR r).1 := by
  unfold countedTargetMinimum
  have hg : ((L : ℝ)≤(Lbar : ℝ) ∧ (mu : ℝ)/2≤(M : ℝ)) ↔ L≤Lbar ∧ mu/2≤M := by
    constructor <;> intro h <;> exact_mod_cast h
  by_cases h : L≤Lbar ∧ mu/2≤M
  · rw [if_pos h,if_pos (hg.mpr h)]
    dsimp only
    rw [Rat.cast_max,foldCountedMinValue,castFoldMin,foldCountedMinValue]
    simp only [List.map_ofFn,Function.comp_def,Rat.cast_div,Rat.cast_add,Rat.cast_one,
      Rat.cast_ofNat,Rat.cast_natCast,ht]
  · rw [if_neg h,if_neg (fun h' => h (hg.mp h'))]
    simp only [Rat.cast_div,Rat.cast_ofNat]

lemma countedKnotScan_ratCast (v : ℕ → ℚ) (ρ : ℚ) (j k : ℕ) :
    countedKnotScan (fun i => (v i : ℝ)) (ρ : ℝ) j k=countedKnotScan v ρ j k := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    simp only [countedKnotScan,Rat.cast_le,ih]

lemma countedCalibrationGridSize_ratCast (m : ℕ) (zlo zhi : ℚ) :
    countedCalibrationGridSize m (zlo : ℝ) (zhi : ℝ)=countedCalibrationGridSize m zlo zhi := by
  unfold countedCalibrationGridSize
  have h := countedKnotScan_ratCast (fun j : ℕ => (j : ℚ)) ((m : ℚ)*(zhi-zlo)) 0 m
  simp only [Rat.cast_natCast,Rat.cast_mul,Rat.cast_sub] at h
  rw [h]

lemma storedCalibrationCoefficient_ratCast (J : ℕ) (zlo zhi : ℚ) (k : ℕ) :
    ((storedCalibrationCoefficient J zlo zhi k : ℚ) : ℝ) =
      storedCalibrationCoefficient J (zlo : ℝ) (zhi : ℝ) k := by
  have hGet {K : Type} {n : ℕ} (f : Fin n → K) (i : Fin n) :
      (Vector.ofFn f).get i=f i := Vector.getElem_ofFn i.isLt
  simp only [storedCalibrationCoefficient,hGet]
  change ((zlo+((coefficientIndex J k).val : ℚ)/(J : ℚ)*(zhi-zlo) : ℚ) : ℝ) =
    (zlo : ℝ)+((coefficientIndex J k).val : ℝ)/(J : ℝ)*((zhi : ℝ)-(zlo : ℝ))
  simp only [Rat.cast_add,Rat.cast_div,Rat.cast_natCast,Rat.cast_mul,Rat.cast_sub]

lemma calibrationArrayCast_getD (a : Array ℚ) (j : ℕ) (d : ℚ) :
    ((a[j]?.getD d : ℚ) : ℝ)=((calibrationArrayCast a)[j]?).getD (d : ℝ) := by
  simp only [calibrationArrayCast,Array.getElem?_map,Option.getD_map]

lemma countedCalibrationKnots_ratCast (duration : Fin m → Array ℚ) (J : ℕ) :
    calibrationArrayCast (countedCalibrationKnots duration J)=
      countedCalibrationKnots (fun a => calibrationArrayCast (duration a)) J := by
  unfold calibrationArrayCast countedCalibrationKnots
  rw [Array.map_ofFn]
  congr 1
  funext k
  simp only [Function.comp_def]
  split_ifs
  · exact Rat.cast_zero
  · rw [Rat.cast_mul,Rat.cast_inv,Rat.cast_natCast,Rat.cast_sum]
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    simpa only [Rat.cast_one,calibrationArrayCast] using calibrationArrayCast_getD (duration a) (k.val-1) 1
  · exact Rat.cast_one

def calibrationProfileCast (v : CalibrationRankProfile n J ℚ PSeed) :
    CalibrationRankProfile n J ℝ PSeed :=
  (v.1,(fun i => (v.2.1 i : ℝ)),(fun i => (v.2.2.1 i : ℝ)),v.2.2.2)

theorem countedCalibrationPrepare_ratCast (mu zlo zhi Lbar : ℚ)
    (target : ℚ → TSeed → ℚ × ℕ) (targetR : ℝ → TSeed → ℝ × ℕ)
    (estimate : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ × ℕ)
    (estimateR : Finset (Fin n) → ℝ → ℝ → PSeed → ℝ × ℕ)
    (ht : ∀ z s, ((target z s).1 : ℝ)=(targetR (z : ℝ) s).1)
    (he : ∀ A u z s, ((estimate A u z s).1 : ℝ)=(estimateR A (u : ℝ) (z : ℝ) s).1)
    (q : Fin n → Fin m → ℚ) (r : TargetGrid m → TSeed)
    (profile : Fin m → CalibrationRankProfile n J ℚ PSeed) :
    let out := countedCalibrationPrepare mu zlo zhi Lbar target estimate q r profile
    let outR := countedCalibrationPrepare (mu : ℝ) (zlo : ℝ) (zhi : ℝ) (Lbar : ℝ)
      targetR estimateR (calibrationRowsCast q) r (fun i => calibrationProfileCast (profile i))
    outR.rows=calibrationRowsCast out.rows ∧
      outR.fallback=out.fallback ∧ outR.selection=(out.selection.1,(out.selection.2 : ℝ)) := by
  let qR := calibrationRowsCast q
  let M := (countedEmpiricalMaximum (empiricalStoredRows q)).1
  let MR := (countedEmpiricalMaximum (empiricalStoredRows qR)).1
  let L := ∑ i : Fin n, plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows q)).1 i
  let LR := ∑ i : Fin n, plannerProbabilityRead (countedPlannerProbabilities (plannerStoredRows qR)).1 i
  have hM : (M : ℝ)=MR := countedEmpiricalMaximum_ratCast q
  have hL : (L : ℝ)=LR := by
    unfold L LR
    rw [Rat.cast_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [← plannerProbabilityRead_ratCast,plannerRowsRatCast_ofFn]
    rfl
  let b := decide (Lbar<L ∨ 1/4<M)
  let bR := decide ((Lbar : ℝ)<LR ∨ 1/4<MR)
  have hb : bR=b := by
    apply decide_eq_decide.mpr
    rw [← hL,← hM,← show ((1/4 : ℚ) : ℝ)=(1/4 : ℝ) by norm_num,Rat.cast_lt,Rat.cast_lt]
  let rho := (countedTargetMinimum mu L M Lbar target r).1
  let rhoR := (countedTargetMinimum (mu : ℝ) LR MR (Lbar : ℝ) targetR r).1
  have hRho : (rho : ℝ)=rhoR := by
    change (rho : ℝ)=(countedTargetMinimum (mu : ℝ) LR MR (Lbar : ℝ) targetR r).1
    rw [← hL,← hM]
    exact countedTargetMinimum_ratCast mu L M Lbar target targetR ht r
  let z := storedCalibrationCoefficient J zlo zhi
  let zR := storedCalibrationCoefficient J (zlo : ℝ) (zhi : ℝ)
  have hz : (fun k => (z k : ℝ))=zR := funext (storedCalibrationCoefficient_ratCast J zlo zhi)
  let d := fun i : Fin m =>
    let p := profile i
    (countedRankValidationMemo z estimate q b p.1 p.2.1 p.2.2.1 p.2.2.2).1
  let dR := fun i : Fin m =>
    let p := calibrationProfileCast (profile i)
    (countedRankValidationMemo zR estimateR qR bR p.1 p.2.1 p.2.2.1 p.2.2.2).1
  have hd : (fun i => calibrationArrayCast (d i))=dR := by
    funext i
    let p := profile i
    change calibrationArrayCast (countedRankValidationMemo z estimate q b p.1 p.2.1 p.2.2.1 p.2.2.2).1 =
      (countedRankValidationMemo zR estimateR qR bR p.1 (fun j => (p.2.1 j : ℝ))
        (fun j => (p.2.2.1 j : ℝ)) p.2.2.2).1
    rw [← hz,hb]
    exact countedRankValidationMemo_ratCast z estimate estimateR he q b p.1 p.2.1 p.2.2.1 p.2.2.2
  let A := countedCalibrationKnots d J
  let AR := countedCalibrationKnots dR J
  have hA : calibrationArrayCast A=AR := by
    unfold A AR
    rw [countedCalibrationKnots_ratCast,hd]
  let v := fun k : ℕ => (A[k]?).getD 1
  let vR := fun k : ℕ => (AR[k]?).getD 1
  have hv : (fun k => (v k : ℝ))=vR := by
    funext k
    change (v k : ℝ)=(AR[k]?).getD 1
    rw [← hA]
    simpa only [v,Rat.cast_one] using calibrationArrayCast_getD A k 1
  let k := (countedKnotScan v rho 0 (J+2)).1
  let kR := (countedKnotScan vR rhoR 0 (J+2)).1
  have hk : kR=k := by
    unfold kR k
    rw [← hv,← hRho,countedKnotScan_ratCast]
  dsimp only
  unfold countedCalibrationPrepare
  dsimp only
  have hGet {K : Type} {n : ℕ} (f : Fin n → K) (i : Fin n) :
      (Vector.ofFn f).get i=f i := Vector.getElem_ofFn i.isLt
  simp only [hGet]
  change True ∧ bR=b ∧
    (kR,(rhoR-vR (kR-1))/(vR kR-vR (kR-1)))=
      (k,(((rho-v (k-1))/(v k-v (k-1)) : ℚ) : ℝ))
  refine ⟨trivial,hb,?_⟩
  rw [hk,← hv,← hRho]
  simp only [Rat.cast_div,Rat.cast_sub]


def calibrationProfileToRank (p : CalibrationRankProfile n J ℝ PSeed) :
    RankValidationProfile n J PSeed :=
  (p.2.1,p.1,p.2.2.1,p.2.2.2)

theorem countedCalibrationPrepare_eq_rankValidationPrepare [NeZero m] (mu zlo zhi : ℝ)
    (target : TargetEstimator n m TSeed) (targetWork : ℝ → TSeed → ℕ)
    (estimate : ContinuationEstimator n m PSeed)
    (estimateWork : Finset (Fin n) → ℝ → ℝ → PSeed → ℕ)
    (q : Reservoir n m) (r : TargetGrid m → TSeed)
    (profile : Fin m → CalibrationRankProfile n J ℝ PSeed) :
    let out := countedCalibrationPrepare mu zlo zhi (targetCountCutoff m)
      (fun z s => (target q z s,targetWork z s))
      (fun A u z s => (estimate q A u z s,estimateWork A u z s)) q r profile
    (out.rows,out.selection)=rankValidationPrepare mu zlo zhi target estimate
      ((reservoirCoordinates q,r),fun a => calibrationProfileToRank (profile a)) ∧
    out.fallback=decide (familyFallback q) := by
  let τ := fun a : Fin m => rankValidationDuration (J := J) zlo zhi estimate q (calibrationProfileToRank (profile a))
  have hDur (a : Fin m) (j : Fin (J+1)) :
      let p := profile a
      let out := countedRankValidationMemo (familyCoefficient zlo zhi J)
        (fun A u z s => (estimate q A u z s,estimateWork A u z s))
        q (decide (familyFallback q)) p.1 p.2.1 p.2.2.1 p.2.2.2
      (out.1[j.val]?).getD 1=τ a j := by
    let p := profile a
    let out := countedRankValidationMemo (familyCoefficient zlo zhi J)
      (fun A u z s => (estimate q A u z s,estimateWork A u z s))
      q (decide (familyFallback q)) p.1 p.2.1 p.2.2.1 p.2.2.2
    change (out.1[j.val]?).getD 1=τ a j
    have h : out.1.size=J+1 := countedRankValidationMemo_size _ _ _ _ _ _ _ _
    have hj : j.val<out.1.size := by rw [h]; exact j.isLt
    rw [Array.getElem?_eq_getElem hj,Option.getD_some]
    exact countedRankValidationMemo_eq_reportedDuration zlo zhi estimate estimateWork q p.1 p.2.1 p.2.2.1 p.2.2.2 j
  obtain ⟨hq,hf,hs⟩ := countedCalibrationPrepare_selection mu zlo zhi target targetWork estimate estimateWork
    q r profile τ hDur
  refine ⟨?_,hf⟩
  rw [hq,hs]
  unfold rankValidationPrepare
  simp only [MeasurableEquiv.symm_apply_apply]
  rfl

end ProphetSecretary.Statistics.Calibration
