import ProphetSecretary.Statistics.CalibratedValidationProfiles
import Mathlib.Data.List.OfFn

/-!
# Sharing validation continuation queries

A validation profile is offline data. Its table uses the strict arrival
history at each candidate and stores all coefficient prefix maxima in one
scan. Each candidate/coefficient pair therefore requires one estimate, and
each policy duration is a scan for the earliest accepted time.
-/

open ProphetSecretary.Model
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration

variable {n m J : ℕ} {PSeed : Type}

noncomputable def validationPrefix (J : ℕ) (f : ℕ → ℝ) : List ℝ :=
  (List.ofFn (fun j : Fin J => f (j.val+1))).scanl max (f 0)

@[simp] lemma validationPrefix_length (J : ℕ) (f : ℕ → ℝ) :
    (validationPrefix J f).length=J+1 := by simp [validationPrefix]

lemma validationPrefix_get (J : ℕ) (f : ℕ → ℝ) (j : ℕ) (hj : j ≤ J) :
    (validationPrefix J f)[j]'(by simp; omega) =
      (Finset.range (j+1)).sup' ⟨0,by simp⟩ f := by
  have hRec (k : ℕ) (hk : k < J) :
      getElem (validationPrefix J f) (k+1) (by simp; omega) =
        max (getElem (validationPrefix J f) k (by simp; omega)) (f (k+1)) := by
    let l := List.ofFn (fun i : Fin J => f (i.val+1))
    have hl : k < l.length := by simpa [l] using hk
    simp only [validationPrefix,List.getElem_scanl]
    change (l.take (k+1)).foldl max (f 0)=max ((l.take k).foldl max (f 0)) (f (k+1))
    rw [List.take_succ_eq_append_getElem hl,List.foldl_append]
    simp [l]
  induction j with
  | zero => simp [validationPrefix,Finset.range_one]
  | succ j ih =>
    have hj' : j < J := by omega
    rw [hRec j hj',ih (by omega) hRec]
    have hEq : (Finset.range (j+1+1)).sup' ⟨0,by simp⟩ f =
        (insert (j+1) (Finset.range (j+1))).sup' (Finset.insert_nonempty _ _) f :=
      Finset.sup'_congr ⟨0,by simp⟩ Finset.range_add_one (fun _ _ => rfl)
    rw [hEq,Finset.sup'_insert (H := ⟨0,by simp⟩)]
    exact max_comm _ _

/-- Compute one row using a single history and one fresh seed per coefficient. -/
noncomputable def validationPrefixRow (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) (i : Fin n) : Array ℝ :=
  let u := fun l => unitRamp (ω.2.1 l)
  let H := history Finset.univ ω.1 u (u i)
  let A := continuationIdentities q H i
  let s := currentRankFromClock i H
  let h := unitRemaining (u i)
  (validationPrefix J (fun k => estimate q A h (familyCoefficient zlo zhi J k)
    (ω.2.2 (s,coefficientIndex J k)))).toArray

@[simp] lemma validationPrefixRow_size (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) (i : Fin n) :
    (validationPrefixRow zlo zhi estimate q ω i).size=J+1 := by
  simp [validationPrefixRow]

noncomputable def validationPrefixTable (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) : Array (Array ℝ) :=
  Array.ofFn (validationPrefixRow zlo zhi estimate q ω)

@[simp] lemma validationPrefixTable_size (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) :
    (validationPrefixTable zlo zhi estimate q ω).size=n := by simp [validationPrefixTable]

lemma validationPrefixTable_work (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (q : Reservoir n m) (ω : World n (PolicyQueryArray n J PSeed)) :
    (∑ i : Fin n, ((validationPrefixTable zlo zhi estimate q ω)[i.val]'(by simp)).size)=n*(J+1) := by
  simp [validationPrefixTable]

noncomputable def tableAcceptance (zlo zhi : ℝ) (fallback : Bool)
    (table : Array (Array ℝ)) (x u : Fin n → ℝ) (j : Fin (J+1)) (i : Fin n) : Bool :=
  if fallback then decide (x i=1)
  else decide (x i=1 ∨ (0<x i ∧
    max (familyCoefficient zlo zhi J j.val*unitRemaining (u i)) ((table[i.val]?.getD #[])[j.val]?.getD 0)≤x i))

lemma tableAcceptance_eq_action [NeZero m] (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) (j : Fin (J+1)) (i : Fin n) :
    let u := fun l => unitRamp (ω.2.1 l)
    tableAcceptance zlo zhi (decide (familyFallback q)) (validationPrefixTable zlo zhi estimate q ω) ω.1 u j i =
      (numericalFamilyPolicy zlo zhi estimate j).action (q,ω.2.2) Finset.univ ω.1 u i := by
  dsimp only
  simp only [tableAcceptance,Policy.action,numericalFamilyPolicy,decide_eq_true_eq]
  split_ifs with hf
  · rfl
  · unfold cappedHistoryThresholdPolicy
    simp only [familyThreshold,ProphetSecretary.Statistics.nestedContinuation]
    congr 3
    have hi : i.val < (validationPrefixTable zlo zhi estimate q ω).size := by simp
    rw [Array.getElem?_eq_getElem hi,Option.getD_some]
    simp only [validationPrefixTable,Array.getElem_ofFn]
    have hj : j.val < (validationPrefixRow zlo zhi estimate q ω i).size := by simpa using j.isLt
    rw [Array.getElem?_eq_getElem hj,Option.getD_some]
    simp only [validationPrefixRow,List.getElem_toArray]
    rw [validationPrefix_get J _ j.val (by omega)]
    rfl

private lemma le_foldl_min_iff {a b : ℝ} (l : List ℝ) :
    b≤l.foldl min a ↔ b≤a ∧ ∀ x ∈ l,b≤x := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons,ih,le_min_iff,List.mem_cons]
    aesop

/-- Compute all validation durations without recomputing any continuation query. -/
noncomputable def memoValidationDurationsWithGuard (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) (fallback : Bool) : Array ℝ :=
  let u := fun l => unitRamp (ω.2.1 l)
  let table := if fallback then #[] else validationPrefixTable zlo zhi estimate q ω
  Array.ofFn fun j : Fin (J+1) =>
    (List.ofFn fun i : Fin n => if tableAcceptance zlo zhi fallback table ω.1 u j i then u i else 1).foldl min 1

@[simp] lemma memoValidationDurationsWithGuard_size (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) (fallback : Bool) :
    (memoValidationDurationsWithGuard zlo zhi estimate q ω fallback).size=J+1 := by
  simp [memoValidationDurationsWithGuard]

noncomputable def memoValidationDurations [NeZero m] (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) : Array ℝ :=
  memoValidationDurationsWithGuard zlo zhi estimate q ω (decide (familyFallback q))

@[simp] lemma memoValidationDurations_size [NeZero m] (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) :
    (memoValidationDurations zlo zhi estimate q ω).size=J+1 := by simp [memoValidationDurations]

theorem memoValidationDurations_eq [NeZero m] (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m PSeed) (q : Reservoir n m)
    (ω : World n (PolicyQueryArray n J PSeed)) (j : Fin (J+1)) :
    (memoValidationDurations zlo zhi estimate q ω)[j.val]'(by simpa using j.isLt)=
      validationDuration zlo zhi estimate q ω j := by
  let u := fun l => unitRamp (ω.2.1 l)
  let π := numericalFamilyPolicy zlo zhi estimate j
  have hAct (i : Fin n) :
      tableAcceptance zlo zhi (decide (familyFallback q))
        (if decide (familyFallback q) then #[] else validationPrefixTable zlo zhi estimate q ω)
        ω.1 u j i=π.action (q,ω.2.2) Finset.univ ω.1 u i := by
    by_cases h : familyFallback q
    · simp [h,tableAcceptance,π,Policy.action,numericalFamilyPolicy]
    · simpa only [decide_eq_false_iff_not.mpr h,Bool.false_eq_true,if_false] using
        tableAcceptance_eq_action zlo zhi estimate q ω j i
  simp only [memoValidationDurations,memoValidationDurationsWithGuard,Array.getElem_ofFn,validationDuration]
  change (List.ofFn fun i : Fin n => if tableAcceptance zlo zhi (decide (familyFallback q))
    (if decide (familyFallback q) then #[] else validationPrefixTable zlo zhi estimate q ω)
    ω.1 u j i then u i else 1).foldl min 1 = π.stoppingTime (q,ω.2.2) Finset.univ ω.1 u
  simp only [hAct]
  let f (i : Fin n) := if π.action (q,ω.2.2) Finset.univ ω.1 u i=true then u i else 1
  let L := List.ofFn f
  change L.foldl min 1=π.stoppingTime (q,ω.2.2) Finset.univ ω.1 u
  have hL := (le_foldl_min_iff (a := 1) (b := L.foldl min 1) L).mp le_rfl
  apply le_antisymm
  · apply (π.le_stoppingTime_iff _ _ _ _ _).mpr
    refine ⟨hL.1,?_⟩
    intro i hi
    have ha := ((π.mem_accepted (q,ω.2.2) Finset.univ ω.1 u i).mp hi).2
    have hiL : f i ∈ L := List.mem_ofFn.mpr ⟨i,rfl⟩
    have hm := hL.2 _ hiL
    simpa only [f,ha,if_true] using hm
  · apply (le_foldl_min_iff _).mpr
    refine ⟨π.stoppingTime_le_one _ _ _ _,?_⟩
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (show x∈List.ofFn f from hx)
    dsimp only [f]
    by_cases ha : π.action (q,ω.2.2) Finset.univ ω.1 u i=true
    · rw [if_pos ha]
      exact π.stoppingTime_le_of_accepted _ _ _ _ _
        ((π.mem_accepted (q,ω.2.2) Finset.univ ω.1 u i).mpr ⟨Finset.mem_univ i,ha⟩)
    · rw [if_neg ha]
      exact π.stoppingTime_le_one _ _ _ _

end ProphetSecretary.Statistics.Calibration
