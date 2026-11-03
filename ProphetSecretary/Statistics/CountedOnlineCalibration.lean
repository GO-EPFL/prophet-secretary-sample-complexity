import ProphetSecretary.Statistics.RankValidationMemo

/-!
# The counted online prefix calculation

The decision uses the prepared empirical block, one current timestamp and
the identities already observed. The query row is evaluated only up to
the selected coefficient. No permutation or later timestamp is an input.
-/

open ProphetSecretary.Model

namespace ProphetSecretary.Statistics.Calibration

variable {n m J : ℕ} {Value Obs PSeed : Type*}

def onlineContinuationSet [Zero Value] [LT Value] [DecidableLT Value]
    (q : Fin n → Fin m → Value) (H : Fin n → Option Obs) (i : Fin n) : Finset (Fin n) :=
  Finset.univ.filter (fun j => j≠i ∧ (H j).isNone=true ∧
    (List.finRange m).any (fun a => decide (0<q j a))=true)

def onlineQueryRank (H : Fin n → Option Obs) (i : Fin n) : Fin n :=
  clockHistoryRank i (Finset.univ.filter (fun j => (H j).isSome=true)).card

def countedPrefixMax [Max Value] (f : ℕ → Value × ℕ) (j : ℕ) : Value × ℕ :=
  let tail := List.ofFn (fun k : Fin j => f (k.val+1))
  tail.foldl (fun a b => (max a.1 b.1,a.2+b.2+2)) (f 0)

private lemma countedPrefixMax_work_le [Max Value] (f : ℕ → Value × ℕ) (j W : ℕ)
    (hW : ∀ k≤j, (f k).2≤W) :
    (countedPrefixMax f j).2≤(j+1)*(W+2) := by
  have hFold (l : List (Value × ℕ)) (a : Value × ℕ) (h : ∀ x ∈ l,x.2≤W) :
      (l.foldl (fun a b => (max a.1 b.1,a.2+b.2+2)) a).2≤a.2+l.length*(W+2) := by
    induction l generalizing a with
    | nil => simp
    | cons x l ih =>
      simp only [List.foldl_cons,List.length_cons]
      have h' := ih (max a.1 x.1,a.2+x.2+2) (fun y hy => h y (List.mem_cons_of_mem _ hy))
      have hx := h x List.mem_cons_self
      exact h'.trans (by dsimp only; nlinarith only [hx])
  let l := List.ofFn (fun k : Fin j => f (k.val+1))
  have h := hFold l (f 0) (fun a ha => by
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp (show a∈List.ofFn _ from ha)
    exact hW _ (by omega))
  have hl : l.length=j := by simp [l]
  rw [hl] at h
  have hz := hW 0 (Nat.zero_le _)
  exact h.trans (by nlinarith only [hz])

/-- The fallback and the cap and zero branches need no continuation query. -/
def countedOnlineCalibrationDecision [Field Value] [LinearOrder Value]
    (z : ℕ → Value) (estimate : Finset (Fin n) → Value → Value → PSeed → Value × ℕ)
    (q : Fin n → Fin m → Value) (fallback : Bool) (j : Fin (J+1))
    (t x : Value) (H : Fin n → Option Obs) (i : Fin n) (r : PolicyQueryArray n J PSeed) : Bool × ℕ :=
  if fallback then (decide (x=1),2)
  else if x=1 then (true,3)
  else if x≤0 then (false,4)
  else
    let A := onlineContinuationSet q H i
    let k := onlineQueryRank H i
    let u := max 0 (min 1 (1-t))
    let a := countedPrefixMax (fun l => estimate A u (z l) (r (k,coefficientIndex J l))) j.val
    (decide (max (z j.val*u) a.1≤x),n*(m+4)+10+a.2)

lemma countedOnlineCalibrationDecision_work_le [Field Value] [LinearOrder Value]
    (z : ℕ → Value) (estimate : Finset (Fin n) → Value → Value → PSeed → Value × ℕ)
    (q : Fin n → Fin m → Value) (fallback : Bool) (j : Fin (J+1))
    (t x : Value) (H : Fin n → Option Obs) (i : Fin n) (r : PolicyQueryArray n J PSeed) (W : ℕ)
    (hW : ∀ A u z s, (estimate A u z s).2≤W) :
    (countedOnlineCalibrationDecision z estimate q fallback j t x H i r).2≤
      n*(m+4)+10+(J+1)*(W+2) := by
  unfold countedOnlineCalibrationDecision
  split_ifs
  · omega
  · omega
  · omega
  · let A := onlineContinuationSet q H i
    let k := onlineQueryRank H i
    let u := max 0 (min 1 (1-t))
    let F := fun l : ℕ => estimate A u (z l) (r (k,coefficientIndex J l))
    have h := countedPrefixMax_work_le F j.val W (fun _ _ => hW _ _ _ _)
    change n*(m+4)+10+(countedPrefixMax F j.val).2≤_
    exact add_le_add le_rfl (h.trans (Nat.mul_le_mul_right _ (by omega)))

section Agreement
open scoped Classical

lemma onlineContinuationSet_eq (q : Reservoir n m) (H : History n) (i : Fin n) :
    onlineContinuationSet q H i=continuationIdentities q H i := by
  ext j
  cases h : H j <;>
    simp [onlineContinuationSet,continuationIdentities,unseen,h,List.any_eq_true]

lemma onlineQueryRank_eq (H : History n) (i : Fin n) :
    onlineQueryRank H i=currentRankFromClock i H := by
  unfold onlineQueryRank currentRankFromClock
  congr 1
  congr 1
  ext j
  cases h : H j <;> simp [clockHistoryPresent,h]

lemma countedPrefixMax_value (f : ℕ → ℝ × ℕ) (j : ℕ) :
    (countedPrefixMax f j).1=(Finset.range (j+1)).sup' ⟨0,by simp⟩ (fun k => (f k).1) := by
  have hF (l : List (ℝ × ℕ)) (a : ℝ × ℕ) :
      (l.foldl (fun a b => (max a.1 b.1,a.2+b.2+2)) a).1=(l.map Prod.fst).foldl max a.1 := by
    induction l generalizing a with
    | nil => rfl
    | cons b l ih => exact ih (max a.1 b.1,a.2+b.2+2)
  let l := List.ofFn (fun k : Fin j => f (k.val+1))
  have hl : (l.map Prod.fst).length=j := by simp [l]
  have h := validationPrefix_get j (fun k => (f k).1) j le_rfl
  change (l.foldl (fun a b => (max a.1 b.1,a.2+b.2+2)) (f 0)).1=_
  rw [hF]
  simp only [validationPrefix,List.getElem_scanl] at h
  have hL : l.map Prod.fst=List.ofFn (fun k : Fin j => (f (k.val+1)).1) := by
    simp only [l,List.map_ofFn,Function.comp_def]
  have hTake : (l.map Prod.fst).take j=l.map Prod.fst := by
    rw [← hl,List.take_length]
  rw [← hL,hTake] at h
  exact h

theorem countedOnlineCalibrationDecision_eq [NeZero m]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (work : Finset (Fin n) → ℝ → ℝ → PSeed → ℕ)
    (q : Reservoir n m) (r : PolicyQueryArray n J PSeed) (j : Fin (J+1))
    (t x : ℝ) (H : History n) (i : Fin n) :
    (countedOnlineCalibrationDecision (familyCoefficient zlo zhi J)
      (fun A u z s => (estimate q A u z s,work A u z s)) q (decide (familyFallback q)) j t x H i r).1 =
      (numericalFamilyPolicy zlo zhi estimate j).decide (q,r) t i x H := by
  by_cases hf : familyFallback q
  · have hb : decide (familyFallback q)=true := decide_eq_true hf
    simp only [countedOnlineCalibrationDecision,numericalFamilyPolicy,hb,if_true,if_pos hf]
  · have hb : decide (familyFallback q)=false := decide_eq_false_iff_not.mpr hf
    by_cases hx : x=1
    · simp only [countedOnlineCalibrationDecision,numericalFamilyPolicy,hb,Bool.false_eq_true,if_false,
        if_neg hf,cappedHistoryThresholdPolicy,hx,eq_self,if_true,true_or,decide_true]
    · by_cases hx0 : x≤0
      · simp only [countedOnlineCalibrationDecision,numericalFamilyPolicy,hb,Bool.false_eq_true,if_false,
          if_neg hf,if_pos hx0,cappedHistoryThresholdPolicy,hx,not_lt_of_ge hx0,false_and,
          or_self,decide_false]
      · simp only [countedOnlineCalibrationDecision,numericalFamilyPolicy,hb,Bool.false_eq_true,if_false,
          if_neg hf,if_neg hx0,cappedHistoryThresholdPolicy,hx,lt_of_not_ge hx0,true_and,
          false_or,countedPrefixMax_value,onlineContinuationSet_eq,onlineQueryRank_eq]
        rfl

/-- Mapping the payload of an observation does not change the online active identities. -/
lemma onlineContinuationSet_map (q : Reservoir n m) {A B : Type*}
    (H : Fin n → Option A) (f : A → B) (i : Fin n) :
    onlineContinuationSet q (fun j => (H j).map f) i=onlineContinuationSet q H i := by
  ext j
  cases h : H j <;> simp [onlineContinuationSet,h]

lemma onlineQueryRank_map {A B : Type*}
    (H : Fin n → Option A) (f : A → B) (i : Fin n) :
    onlineQueryRank (fun j => (H j).map f) i=onlineQueryRank H i := by
  have h : (Finset.univ.filter (fun j => ((H j).map f).isSome=true))=
      (Finset.univ.filter (fun j => (H j).isSome=true)) := by
    ext j
    cases hj : H j <;> simp [hj]
  rw [onlineQueryRank,onlineQueryRank,h]

theorem countedOnlineCalibrationRankDecision_eq [NeZero m]
    (zlo zhi : ℝ) (estimate : ContinuationEstimator n m PSeed)
    (work : Finset (Fin n) → ℝ → ℝ → PSeed → ℕ)
    (q : Reservoir n m) (r : PolicyQueryArray n J PSeed) (j : Fin (J+1))
    (s : Fin n → ℝ) (k i : Fin n) (x : ℝ) (H : RankHistory n) :
    (countedOnlineCalibrationDecision (familyCoefficient zlo zhi J)
      (fun A u z t => (estimate q A u z t,work A u z t)) q (decide (familyFallback q)) j (s k) x H i r).1 =
      (numericalFamilyPolicy zlo zhi estimate j).clockToRank.decide (s,q,r) k i x H := by
  let F := fun p : Fin n × ℝ => (s p.1,p.2)
  let H' : History n := fun l => (H l).map F
  have h := countedOnlineCalibrationDecision_eq zlo zhi estimate work q r j (s k) x H' i
  change _ = (numericalFamilyPolicy zlo zhi estimate j).decide (q,r) (s k) i x H'
  rw [← h]
  unfold countedOnlineCalibrationDecision
  rw [onlineContinuationSet_map q H F i,onlineQueryRank_map H F i]

end Agreement

end ProphetSecretary.Statistics.Calibration
