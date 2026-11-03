import ProphetSecretary.Statistics.CountedOnlineCalibration
import Mathlib.Data.Rat.Cast.Order

/-!
# Rational values in the counted calibration loops

Casting the rational stored rows, coefficients, timestamps and query
outputs preserves the offline rank scan and the online accept decision.
The arithmetic work bounds are applied directly to the rational loops.
-/

open ProphetSecretary.Model

namespace ProphetSecretary.Statistics.Calibration

variable {n m J : ℕ} {PSeed Obs : Type*}

def calibrationRowsCast (q : Fin n → Fin m → ℚ) : Reservoir n m :=
  fun i a => (q i a : ℝ)

def calibrationArrayCast (a : Array ℚ) : Array ℝ :=
  a.map fun x : ℚ => (x : ℝ)

lemma onlineContinuationSet_ratCast (q : Fin n → Fin m → ℚ)
    (H : Fin n → Option Obs) (i : Fin n) :
    onlineContinuationSet (calibrationRowsCast q) H i=onlineContinuationSet q H i := by
  ext j
  simp [onlineContinuationSet,calibrationRowsCast,List.any_eq_true]

lemma rankContinuationSet_ratCast (q : Fin n → Fin m → ℚ) (p : Equiv.Perm (Fin n)) (k : Fin n) :
    rankContinuationSet (calibrationRowsCast q) p k=rankContinuationSet q p k := by
  ext j
  simp [rankContinuationSet,calibrationRowsCast,List.any_eq_true]

private lemma cast_unitRemaining (t : ℚ) :
    ((max 0 (min 1 (1-t)) : ℚ) : ℝ)=max 0 (min 1 (1-(t : ℝ))) := by
  simp only [Rat.cast_max,Rat.cast_min,Rat.cast_zero,Rat.cast_one,Rat.cast_sub]

private lemma cast_scanl_max (l : List ℚ) (a : ℚ) :
    (l.scanl max a).map (fun x : ℚ => (x : ℝ))=(l.map (fun x : ℚ => (x : ℝ))).scanl max (a : ℝ) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih => simp only [List.scanl_cons,List.map_cons,ih,Rat.cast_max]

private lemma foldl_countedMax_value {K : Type*} [Max K] (l : List (K × ℕ)) (a : K × ℕ) :
    (l.foldl (fun a b => (max a.1 b.1,a.2+b.2+2)) a).1=(l.map Prod.fst).foldl max a.1 := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact ih (max a.1 b.1,a.2+b.2+2)

private lemma cast_foldl_max (l : List ℚ) (a : ℚ) :
    ((l.foldl max a : ℚ) : ℝ)=(l.map (fun x : ℚ => (x : ℝ))).foldl max (a : ℝ) := by
  induction l generalizing a with
  | nil => rfl
  | cons x l ih => simp only [List.foldl_cons,List.map_cons,ih,Rat.cast_max]

lemma countedPrefixMax_ratCast (f : ℕ → ℚ × ℕ) (g : ℕ → ℝ × ℕ) (j : ℕ)
    (h : ∀ l, ((f l).1 : ℝ)=(g l).1) :
    ((countedPrefixMax f j).1 : ℝ)=(countedPrefixMax g j).1 := by
  unfold countedPrefixMax
  rw [foldl_countedMax_value,foldl_countedMax_value,cast_foldl_max,h 0]
  simp only [List.map_ofFn,Function.comp_def,h]

theorem countedRankPrefixRow_ratCast (z : ℕ → ℚ)
    (estimate : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ × ℕ)
    (estimateR : Finset (Fin n) → ℝ → ℝ → PSeed → ℝ × ℕ)
    (he : ∀ A u c r, ((estimate A u c r).1 : ℝ)=(estimateR A (u : ℝ) (c : ℝ) r).1)
    (q : Fin n → Fin m → ℚ) (p : Equiv.Perm (Fin n)) (s : Fin n → ℚ)
    (r : PolicyQueryArray n J PSeed) (k : Fin n) :
    calibrationArrayCast (countedRankPrefixRow z estimate q p s r k).1 =
      (countedRankPrefixRow (fun l => (z l : ℝ)) estimateR (calibrationRowsCast q)
        p (fun i => (s i : ℝ)) r k).1 := by
  let A := rankContinuationSet q p k
  let u := max 0 (min 1 (1-s k))
  let f := fun l : ℕ => estimate A u (z l) (r (k,coefficientIndex J l))
  let g := fun l : ℕ => estimateR A (max 0 (min 1 (1-(s k : ℝ)))) (z l : ℝ) (r (k,coefficientIndex J l))
  have h (l : ℕ) : ((f l).1 : ℝ)=(g l).1 := by
    unfold f g
    rw [he,cast_unitRemaining]
  unfold countedRankPrefixRow calibrationArrayCast
  rw [rankContinuationSet_ratCast]
  change ((List.scanl max (f 0).1 ((List.ofFn (fun l : Fin J => f (l.val+1))).map Prod.fst)).toArray.map
    (fun x : ℚ => (x : ℝ))) =
    (List.scanl max (g 0).1 ((List.ofFn (fun l : Fin J => g (l.val+1))).map Prod.fst)).toArray
  rw [List.map_toArray,cast_scanl_max,h 0]
  simp only [List.map_ofFn,Function.comp_def,h]

private lemma optionArrayRead_ratCast (a : Array ℚ) (j : ℕ) (d : ℚ) :
    ((a[j]?.getD d : ℚ) : ℝ)=((calibrationArrayCast a)[j]?).getD (d : ℝ) := by
  simp only [calibrationArrayCast,Array.getElem?_map,Option.getD_map]

lemma rankMemoAccepts_ratCast (z : ℕ → ℚ) (fallback : Bool)
    (rows : Array (Array ℚ)) (x s : Fin n → ℚ) (p : Equiv.Perm (Fin n))
    (j : Fin (J+1)) (k : Fin n) :
    rankMemoAccepts z fallback rows x s p j k =
      rankMemoAccepts (fun l => (z l : ℝ)) fallback (rows.map calibrationArrayCast)
        (fun i => (x i : ℝ)) (fun i => (s i : ℝ)) p j k := by
  have hRead : ((((rows[k.val]?.getD #[])[j.val]?.getD 0) : ℚ) : ℝ) =
      (((rows.map calibrationArrayCast)[k.val]?.getD #[])[j.val]?.getD 0) := by
    have hOuter : ((rows.map calibrationArrayCast)[k.val]?).getD #[]=
        calibrationArrayCast (rows[k.val]?.getD #[]) := by
      rw [Array.getElem?_map]
      cases hh : rows[k.val]? <;> simp [calibrationArrayCast]
    rw [hOuter]
    simpa only [Rat.cast_zero] using optionArrayRead_ratCast (rows[k.val]?.getD #[]) j.val 0
  have hCap : ((x (p k) : ℚ) : ℝ)=1 ↔ x (p k)=1 := by norm_cast
  have hVal : ((max (z j.val * max 0 (min 1 (1-s k)))
      (((rows[k.val]?.getD #[])[j.val]?.getD 0)) : ℚ) : ℝ) =
    max ((z j.val : ℝ) * max 0 (min 1 (1-(s k : ℝ))))
      (((rows.map calibrationArrayCast)[k.val]?.getD #[])[j.val]?.getD 0) := by
    rw [Rat.cast_max,Rat.cast_mul,cast_unitRemaining,hRead]
  unfold rankMemoAccepts
  split_ifs
  · exact decide_eq_decide.mpr hCap.symm
  · apply decide_eq_decide.mpr
    rw [hCap,←hVal,Rat.cast_pos,Rat.cast_le]

theorem countedRankValidationMemo_ratCast (z : ℕ → ℚ)
    (estimate : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ × ℕ)
    (estimateR : Finset (Fin n) → ℝ → ℝ → PSeed → ℝ × ℕ)
    (he : ∀ A u c r, ((estimate A u c r).1 : ℝ)=(estimateR A (u : ℝ) (c : ℝ) r).1)
    (q : Fin n → Fin m → ℚ) (fallback : Bool)
    (p : Equiv.Perm (Fin n)) (x s : Fin n → ℚ) (r : PolicyQueryArray n J PSeed) :
    calibrationArrayCast (countedRankValidationMemo z estimate q fallback p x s r).1 =
      (countedRankValidationMemo (fun l => (z l : ℝ)) estimateR (calibrationRowsCast q)
        fallback p (fun i => (x i : ℝ)) (fun i => (s i : ℝ)) r).1 := by
  let rows := (if fallback then #[] else Array.ofFn (countedRankPrefixRow z estimate q p s r)).map Prod.fst
  let rowsR := (if fallback then #[] else Array.ofFn (countedRankPrefixRow
    (fun l => (z l : ℝ)) estimateR (calibrationRowsCast q) p (fun i => (s i : ℝ)) r)).map Prod.fst
  have hr : rows.map calibrationArrayCast=rowsR := by
    cases fallback
    · simp only [rows,rowsR,Bool.false_eq_true,if_false,Array.map_ofFn,Function.comp_def,
        countedRankPrefixRow_ratCast z estimate estimateR he q p s r]
    · simp [rows,rowsR]
  have hPred (j : Fin (J+1)) : rankMemoAccepts z fallback rows x s p j =
      rankMemoAccepts (fun l => (z l : ℝ)) fallback rowsR
        (fun i => (x i : ℝ)) (fun i => (s i : ℝ)) p j := by
    funext k
    rw [← hr]
    exact rankMemoAccepts_ratCast z fallback rows x s p j k
  change (Array.ofFn (fun j : Fin (J+1) =>
      ((List.finRange n).find? (rankMemoAccepts z fallback rows x s p j)).elim 1 s)).map
        (fun x : ℚ => (x : ℝ)) =
    Array.ofFn (fun j : Fin (J+1) =>
      ((List.finRange n).find? (rankMemoAccepts (fun l => (z l : ℝ)) fallback rowsR
        (fun i => (x i : ℝ)) (fun i => (s i : ℝ)) p j)).elim 1 (fun i => (s i : ℝ)))
  rw [Array.map_ofFn]
  congr 1
  funext j
  simp only [Function.comp_def,hPred]
  cases (List.finRange n).find? _ <;> simp

theorem countedOnlineCalibrationDecision_ratCast (z : ℕ → ℚ)
    (estimate : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ × ℕ)
    (estimateR : Finset (Fin n) → ℝ → ℝ → PSeed → ℝ × ℕ)
    (he : ∀ A u c r, ((estimate A u c r).1 : ℝ)=(estimateR A (u : ℝ) (c : ℝ) r).1)
    (q : Fin n → Fin m → ℚ) (fallback : Bool) (j : Fin (J+1))
    (t x : ℚ) (H : Fin n → Option Obs) (i : Fin n) (r : PolicyQueryArray n J PSeed) :
    (countedOnlineCalibrationDecision z estimate q fallback j t x H i r).1 =
      (countedOnlineCalibrationDecision (fun l => (z l : ℝ)) estimateR (calibrationRowsCast q)
        fallback j (t : ℝ) (x : ℝ) H i r).1 := by
  let A := onlineContinuationSet q H i
  let u := max 0 (min 1 (1-t))
  let f := fun l : ℕ => estimate A u (z l) (r (onlineQueryRank H i,coefficientIndex J l))
  let g := fun l : ℕ => estimateR A (max 0 (min 1 (1-(t : ℝ)))) (z l : ℝ) (r (onlineQueryRank H i,coefficientIndex J l))
  have h (l : ℕ) : ((f l).1 : ℝ)=(g l).1 := by
    unfold f g
    rw [he,cast_unitRemaining]
  have hVal : ((max (z j.val*u) (countedPrefixMax f j.val).1 : ℚ) : ℝ) =
      max ((z j.val : ℝ)*max 0 (min 1 (1-(t : ℝ)))) (countedPrefixMax g j.val).1 := by
    rw [Rat.cast_max,Rat.cast_mul,cast_unitRemaining,countedPrefixMax_ratCast f g j.val h]
  have hCap : ((x : ℝ)=1) ↔ x=1 := by norm_cast
  have hZero : ((x : ℝ)≤0) ↔ x≤0 := by norm_cast
  unfold countedOnlineCalibrationDecision
  by_cases hb : fallback=true
  · simp only [hb,if_true]
    exact decide_eq_decide.mpr hCap.symm
  · rw [if_neg hb,if_neg hb]
    by_cases hx : x=1
    · rw [if_pos hx,if_pos (hCap.mpr hx)]
    · rw [if_neg hx,if_neg (fun h => hx (hCap.mp h))]
      by_cases h0 : x≤0
      · rw [if_pos h0,if_pos (hZero.mpr h0)]
      · rw [if_neg h0,if_neg (fun h => h0 (hZero.mp h)),onlineContinuationSet_ratCast]
        change decide (max (z j.val*u) (countedPrefixMax f j.val).1≤x) =
          decide (max ((z j.val : ℝ)*max 0 (min 1 (1-(t : ℝ)))) (countedPrefixMax g j.val).1≤(x : ℝ))
        apply decide_eq_decide.mpr
        rw [← hVal,Rat.cast_le]

end ProphetSecretary.Statistics.Calibration
