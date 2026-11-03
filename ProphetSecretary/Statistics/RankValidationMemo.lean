import ProphetSecretary.Statistics.CalibratedValidationMemo
import ProphetSecretary.Statistics.CalibratedPreparedPolicy
import ProphetSecretary.Model.ClockAnnotations
import Mathlib.Data.List.FinRange

/-!
# A memoized validation trajectory in arrival rank order

The trajectory is already offline data. Each rank computes its active
continuation set once, and all grid coefficients share a prefix-max row.
For each endpoint a first-acceptance scan follows rank order even when
two assigned timestamps coincide.
-/

open ProphetSecretary.Model

namespace ProphetSecretary.Statistics.Calibration

variable {n m J : ℕ} {PSeed Value : Type*}

def rankContinuationSet [Zero Value] [LT Value] [DecidableLT Value]
    (q : Fin n → Fin m → Value) (p : Equiv.Perm (Fin n)) (k : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => k<p.symm i ∧ (List.finRange m).any (fun a => decide (0<q i a))=true)

def countedRankPrefixRow [Field Value] [LinearOrder Value]
    (z : ℕ → Value) (estimate : Finset (Fin n) → Value → Value → PSeed → Value × ℕ)
    (q : Fin n → Fin m → Value) (p : Equiv.Perm (Fin n)) (s : Fin n → Value)
    (r : PolicyQueryArray n J PSeed) (k : Fin n) : Array Value × ℕ :=
  let A := rankContinuationSet q p k
  let u := max 0 (min 1 (1-s k))
  let call := fun l : ℕ => estimate A u (z l) (r (k,coefficientIndex J l))
  let a := call 0
  let tail := List.ofFn (fun l : Fin J => call (l.val+1))
  let values := ((tail.map Prod.fst).scanl max a.1).toArray
  let work := tail.foldl (fun w b => w+b.2+1) a.2
  (values,n*(m+2)+6+work+J+1)

@[simp] lemma countedRankPrefixRow_size [Field Value] [LinearOrder Value]
    (z : ℕ → Value) (estimate : Finset (Fin n) → Value → Value → PSeed → Value × ℕ)
    (q : Fin n → Fin m → Value) (p : Equiv.Perm (Fin n)) (s : Fin n → Value)
    (r : PolicyQueryArray n J PSeed) (k : Fin n) :
    (countedRankPrefixRow z estimate q p s r k).1.size=J+1 := by simp [countedRankPrefixRow]

private lemma foldl_work_le {α : Type*} (l : List (α × ℕ)) (W a : ℕ)
    (hW : ∀ x ∈ l, x.2≤W) :
    l.foldl (fun w b => w+b.2+1) a≤a+l.length*(W+1) := by
  induction l generalizing a with
  | nil => simp
  | cons x l ih =>
    simp only [List.foldl_cons,List.length_cons]
    have h := ih (a+x.2+1) (fun y hy => hW y (List.mem_cons_of_mem _ hy))
    exact h.trans (by have hx := hW x (List.mem_cons_self); nlinarith only [hx])

lemma countedRankPrefixRow_work_le [Field Value] [LinearOrder Value]
    (z : ℕ → Value) (estimate : Finset (Fin n) → Value → Value → PSeed → Value × ℕ)
    (q : Fin n → Fin m → Value) (p : Equiv.Perm (Fin n)) (s : Fin n → Value)
    (r : PolicyQueryArray n J PSeed) (k : Fin n) (W : ℕ)
    (hW : ∀ A u z r, (estimate A u z r).2≤W) :
    (countedRankPrefixRow z estimate q p s r k).2≤n*(m+2)+6+(J+1)*(W+2) := by
  let A := rankContinuationSet q p k
  let u := max 0 (min 1 (1-s k))
  let call := fun l : ℕ => estimate A u (z l) (r (k,coefficientIndex J l))
  let L := List.ofFn (fun l : Fin J => call (l.val+1))
  have hL : ∀ x ∈ L, x.2≤W := by
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp (show x∈List.ofFn _ from hx)
    exact hW _ _ _ _
  have h := foldl_work_le L W (call 0).2 hL
  have hlen : L.length=J := by simp [L]
  rw [hlen] at h
  have h0 : (call 0).2≤W := hW _ _ _ _
  change n*(m+2)+6+L.foldl (fun w b => w+b.2+1) (call 0).2+J+1≤_
  nlinarith only [h,h0]

/-- Array lookups and comparisons at the current rank use the precomputed row. -/
def rankMemoAccepts [Field Value] [LinearOrder Value] (z : ℕ → Value) (fallback : Bool)
    (rows : Array (Array Value)) (x s : Fin n → Value) (p : Equiv.Perm (Fin n))
    (j : Fin (J+1)) (k : Fin n) : Bool :=
  let a := x (p k)
  if fallback then decide (a=1)
  else decide (a=1 ∨ (0<a ∧
    max (z j.val*max 0 (min 1 (1-s k))) ((rows[k.val]?.getD #[])[j.val]?.getD 0)≤a))

def countedRankValidationMemo [Field Value] [LinearOrder Value]
    (z : ℕ → Value) (estimate : Finset (Fin n) → Value → Value → PSeed → Value × ℕ)
    (q : Fin n → Fin m → Value) (fallback : Bool)
    (p : Equiv.Perm (Fin n)) (x s : Fin n → Value) (r : PolicyQueryArray n J PSeed) : Array Value × ℕ :=
  let table := if fallback then #[] else Array.ofFn (countedRankPrefixRow z estimate q p s r)
  let rows := table.map Prod.fst
  let durations := Array.ofFn (fun j : Fin (J+1) =>
    ((List.finRange n).find? (rankMemoAccepts z fallback rows x s p j)).elim 1 s)
  (durations,table.foldl (fun c row => c+row.2+1) 0+(J+1)*(12*n+3))

@[simp] lemma countedRankValidationMemo_size [Field Value] [LinearOrder Value]
    (z : ℕ → Value) (estimate : Finset (Fin n) → Value → Value → PSeed → Value × ℕ)
    (q : Fin n → Fin m → Value) (fallback : Bool)
    (p : Equiv.Perm (Fin n)) (x s : Fin n → Value) (r : PolicyQueryArray n J PSeed) :
    (countedRankValidationMemo z estimate q fallback p x s r).1.size=J+1 := by
  simp [countedRankValidationMemo]

lemma countedRankValidationMemo_work_le [Field Value] [LinearOrder Value]
    (z : ℕ → Value) (estimate : Finset (Fin n) → Value → Value → PSeed → Value × ℕ)
    (q : Fin n → Fin m → Value) (fallback : Bool)
    (p : Equiv.Perm (Fin n)) (x s : Fin n → Value) (r : PolicyQueryArray n J PSeed) (W : ℕ)
    (hW : ∀ A u z r, (estimate A u z r).2≤W) :
    (countedRankValidationMemo z estimate q fallback p x s r).2≤
      n*(n*(m+2)+7+(J+1)*(W+2))+(J+1)*(12*n+3) := by
  by_cases h : fallback=true
  · simp only [countedRankValidationMemo,h,if_true,Array.foldl_empty,zero_add]
    exact Nat.le_add_left _ _
  · have hf : fallback=false := Bool.eq_false_iff.mpr h
    let table := Array.ofFn (countedRankPrefixRow z estimate q p s r)
    have hRow : ∀ row ∈ table.toList, row.2≤n*(m+2)+6+(J+1)*(W+2) := by
      intro row hrow
      have hE : table.toList=List.ofFn (countedRankPrefixRow z estimate q p s r) := by simp [table]
      rw [hE] at hrow
      obtain ⟨k,rfl⟩ := List.mem_ofFn.mp hrow
      exact countedRankPrefixRow_work_le z estimate q p s r k W hW
    have hCost := foldl_work_le table.toList (n*(m+2)+6+(J+1)*(W+2)) 0 hRow
    simp only [Array.length_toList,Array.foldl_toList,zero_add] at hCost
    have hSize : table.size=n := by simp [table]
    rw [hSize] at hCost
    simp only [countedRankValidationMemo,hf,Bool.false_eq_true,if_false]
    change table.foldl (fun c row => c+row.2+1) 0+(J+1)*(12*n+3)≤_
    have hEq : table.foldl (fun c row => c+row.2+1) 0 =
        table.foldl (fun c row => c+row.2+1) 0 0 n := by rw [hSize]
    rw [hEq]
    have hRewrite : n*(n*(m+2)+6+(J+1)*(W+2)+1)=n*(n*(m+2)+7+(J+1)*(W+2)) := by ring
    exact add_le_add (hCost.trans_eq hRewrite) le_rfl


section ExecutionAgreement

open scoped Classical

variable {RSeed : Type}

noncomputable def rankAnnotatedHistory (p : Equiv.Perm (Fin n)) (x s : Fin n → ℝ) (k : Fin n) : History n :=
  fun j => (rankHistory p x k j).map (fun a => (s a.1,a.2))

lemma rankAnnotatedHistory_continuationSet (q : Reservoir n m)
    (p : Equiv.Perm (Fin n)) (x s : Fin n → ℝ) (k : Fin n) :
    continuationIdentities q (rankAnnotatedHistory p x s k) (p k)=rankContinuationSet q p k := by
  ext j
  have hId : p.symm j=k ↔ j=p k := by
    constructor
    · intro h
      rw [← h,Equiv.apply_symm_apply]
    · intro h
      rw [h,Equiv.symm_apply_apply]
  have hRank : (j≠p k ∧ ¬p.symm j<k) ↔ k<p.symm j := by
    change ((¬j=p k) ∧ ¬p.symm j<k) ↔ k<p.symm j
    rw [← hId]
    omega
  have hNone : rankAnnotatedHistory p x s k j=none ↔ ¬p.symm j<k := by
    by_cases h : p.symm j<k <;> simp [rankAnnotatedHistory,rankHistory,h]
  simp only [continuationIdentities,Finset.mem_filter,Finset.mem_erase,unseen,Finset.mem_univ,
    true_and,hNone,rankContinuationSet,List.any_eq_true,List.mem_finRange,decide_eq_true_eq]
  simp only [hRank]

lemma rankAnnotatedHistory_currentRank (p : Equiv.Perm (Fin n)) (x s : Fin n → ℝ) (k : Fin n) :
    currentRankFromClock (p k) (rankAnnotatedHistory p x s k)=k := by
  have h : clockHistoryPresent (rankAnnotatedHistory p x s k)=
      Finset.univ.filter (fun j=>p.symm j<k) := by
    ext j
    by_cases hj : p.symm j<k <;> simp [clockHistoryPresent,rankAnnotatedHistory,rankHistory,hj]
  rw [currentRankFromClock,h,card_filter_permutation_lt,clockHistoryRank_of_fin]

lemma countedRankPrefixRow_value (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m RSeed)
    (work : Finset (Fin n) → ℝ → ℝ → RSeed → ℕ)
    (q : Reservoir n m) (p : Equiv.Perm (Fin n)) (x s : Fin n → ℝ)
    (r : PolicyQueryArray n J RSeed) (k : Fin n) :
    (countedRankPrefixRow (familyCoefficient zlo zhi J)
        (fun A u z b => (estimate q A u z b,work A u z b)) q p s r k).1 =
      (validationPrefix J (familyQuery zlo zhi estimate (q,r) (s k) (p k)
        (rankAnnotatedHistory p x s k))).toArray := by
  simp only [countedRankPrefixRow,validationPrefix,List.map_ofFn,familyQuery,
    rankAnnotatedHistory_continuationSet,rankAnnotatedHistory_currentRank,unitRemaining,Function.comp_def]

lemma rankMemoAccepts_eq_action [NeZero m] (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m RSeed)
    (work : Finset (Fin n) → ℝ → ℝ → RSeed → ℕ)
    (q : Reservoir n m) (p : Equiv.Perm (Fin n)) (x s : Fin n → ℝ)
    (r : PolicyQueryArray n J RSeed) (k : Fin n) (j : Fin (J+1)) :
    let fallback := decide (familyFallback q)
    let z := familyCoefficient zlo zhi J
    let table := if fallback then #[] else
      Array.ofFn (countedRankPrefixRow z (fun A u c b => (estimate q A u c b,work A u c b)) q p s r)
    rankMemoAccepts z fallback (table.map Prod.fst) x s p j k =
      (frozenFamilyPolicy zlo zhi estimate q j).clockToRank.action (s,r) p x (p k) := by
  let H := rankAnnotatedHistory p x s k
  let z := familyCoefficient zlo zhi J
  let call := fun A u c b => (estimate q A u c b,work A u c b)
  let table := Array.ofFn (countedRankPrefixRow z call q p s r)
  change rankMemoAccepts z (decide (familyFallback q)) ((if decide (familyFallback q) then #[] else table).map Prod.fst)
    x s p j k =
    (numericalFamilyPolicy zlo zhi estimate j).decide (q,r) (s (p.symm (p k))) (p k) (x (p k))
      (rankAnnotatedHistory p x s (p.symm (p k)))
  rw [Equiv.symm_apply_apply]
  by_cases hf : familyFallback q
  · have hd : decide (familyFallback q)=true := decide_eq_true hf
    simp only [rankMemoAccepts,numericalFamilyPolicy,if_pos hf,hd,if_true]
  · have hd : decide (familyFallback q)=false := decide_eq_false_iff_not.mpr hf
    simp only [rankMemoAccepts,numericalFamilyPolicy,if_neg hf,hd,Bool.false_eq_true,if_false,cappedHistoryThresholdPolicy]
    have hSize : k.val<(table.map Prod.fst).size := by simp [table]
    rw [Array.getElem?_eq_getElem hSize,Option.getD_some]
    simp only [table,Array.getElem_map,Array.getElem_ofFn,Fin.eta]
    have hRow : (countedRankPrefixRow z call q p s r k).1 =
        (validationPrefix J (familyQuery zlo zhi estimate (q,r) (s k) (p k) H)).toArray :=
      countedRankPrefixRow_value zlo zhi estimate work q p x s r k
    rw [hRow]
    have hS : j.val < (validationPrefix J (familyQuery zlo zhi estimate (q,r) (s k) (p k) H)).toArray.size := by
      rw [List.size_toArray,validationPrefix_length]
      exact j.isLt
    rw [Array.getElem?_eq_getElem hS,Option.getD_some,List.getElem_toArray,
      validationPrefix_get J _ j.val (by omega)]
    rfl

theorem countedRankValidationMemo_eq_reportedDuration [NeZero m] (zlo zhi : ℝ)
    (estimate : ContinuationEstimator n m RSeed)
    (work : Finset (Fin n) → ℝ → ℝ → RSeed → ℕ)
    (q : Reservoir n m) (p : Equiv.Perm (Fin n)) (x s : Fin n → ℝ)
    (r : PolicyQueryArray n J RSeed) (j : Fin (J+1)) :
    let result := countedRankValidationMemo (familyCoefficient zlo zhi J)
      (fun A u z b => (estimate q A u z b,work A u z b)) q (decide (familyFallback q)) p x s r
    result.1[j.val]'(by
      have hS : result.1.size=J+1 := countedRankValidationMemo_size _ _ _ _ _ _ _ _
      rw [hS]
      exact j.isLt) =
      (frozenFamilyPolicy zlo zhi estimate q j).clockToRank.reportedDuration (s,r) p x s := by
  let π := (frozenFamilyPolicy zlo zhi estimate q j).clockToRank
  let a (k : Fin n) := π.action (s,r) p x (p k)
  simp only [countedRankValidationMemo,Array.getElem_ofFn]
  simp only [rankMemoAccepts_eq_action]
  change ((List.finRange n).find? a).elim 1 s=π.reportedDuration (s,r) p x s
  cases h : (List.finRange n).find? a with
  | none =>
    simp only [Option.elim_none]
    apply Eq.symm
    apply π.reportedDuration_eq_one_of_no_selection
    intro i hi
    have hA := List.find?_eq_none.mp h (p.symm i) (List.mem_finRange _)
    have hAct := (π.mem_accepted (s,r) p x i).mp hi.1
    apply hA
    simpa only [a,Equiv.apply_symm_apply] using hAct
  | some k =>
    simp only [Option.elim_some]
    apply Eq.symm
    have hFirst := List.find?_eq_some_iff_getElem.mp h
    have hSel : π.Selects (s,r) p x (p k) := by
      refine ⟨(π.mem_accepted (s,r) p x (p k)).mpr hFirst.1,?_⟩
      intro i hi
      rw [Equiv.symm_apply_apply]
      by_contra hn
      have hlt : p.symm i<k := lt_of_not_ge hn
      obtain ⟨l,hl,hEq,hBefore⟩ := hFirst.2
      have hIndex : l=k.val := by simpa only [List.getElem_finRange,Fin.val_cast] using congrArg Fin.val hEq
      have hBefore' := hBefore (p.symm i).val (by rw [hIndex]; exact hlt)
      have hAct := (π.mem_accepted (s,r) p x i).mp hi
      have hIdx : ((List.finRange n)[(p.symm i).val]'(by simp)) = p.symm i := by
        apply Fin.ext
        simp [List.getElem_finRange]
      rw [hIdx] at hBefore'
      have hFalse : ¬a (p.symm i) := by simpa using hBefore'
      exact hFalse (by simpa only [a,Equiv.apply_symm_apply] using hAct)
    simpa only [Equiv.symm_apply_apply] using π.reportedDuration_eq_of_selects (s,r) p x s hSel

end ExecutionAgreement

end ProphetSecretary.Statistics.Calibration
