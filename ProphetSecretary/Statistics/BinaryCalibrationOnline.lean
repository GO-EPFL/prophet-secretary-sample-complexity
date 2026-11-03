import ProphetSecretary.Statistics.BinaryCalibrationValidation
import ProphetSecretary.Statistics.CountedOnlineCalibration

/-!
# Binary execution at the current arrival

The current rank and the unseen set are computed from observed
identities. The online scan needs only the selected coefficient and
queries through that coefficient.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis
open CalibrationBinaryExpr

variable {n m J : ℕ} {PSeed Obs : Type}

def countedBinaryMaxScan (a : CalibrationBinary) : List (CalibrationBinary×ℕ) → CalibrationBinary×ℕ
  | [] => (a,1)
  | b::l =>
    let q := BinaryRational.countedOperation .maximum a b.1
    let p := countedBinaryMaxScan q.1 l
    (p.1,b.2+q.2+p.2+2)

lemma countedBinaryMaxScan_value (a : CalibrationBinary) (l : List (CalibrationBinary×ℕ)) :
    (countedBinaryMaxScan a l).1.value=(l.map (fun b => b.1.value)).foldl max a.value := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simpa only [countedBinaryMaxScan,List.map_cons,List.foldl_cons,countedCalibrationOp_value,
      rationalCalibrationOp] using ih (BinaryRational.countedOperation .maximum a b.1).1

lemma countedBinaryMaxScan_bounds (a : CalibrationBinary) (l : List (CalibrationBinary×ℕ)) (B W : ℕ)
    (ha : RationalHeight a.value B) (hl : ∀ b∈l,RationalHeight b.1.value B ∧ b.2≤W) :
    RationalHeight (countedBinaryMaxScan a l).1.value B ∧
      (countedBinaryMaxScan a l).2≤1+l.length*(W+3600*(B+2)^3+2) := by
  induction l generalizing a with
  | nil => exact ⟨ha,by simp [countedBinaryMaxScan]⟩
  | cons b l ih =>
    have hb := hl b List.mem_cons_self
    let q := BinaryRational.countedOperation .maximum a b.1
    have hqW := BinaryRational.countedOperation_work .maximum a b.1 B ha hb.1
    have hq : RationalHeight q.1.value B := by
      simp only [q,countedCalibrationOp_value,rationalCalibrationOp]
      simpa only [max_self] using ha.max hb.1
    have hTail := ih q.1 hq (fun c hc => hl c (List.mem_cons_of_mem _ hc))
    refine ⟨hTail.1,?_⟩
    change b.2+q.2+(countedBinaryMaxScan q.1 l).2+2≤_
    change q.2≤_ at hqW
    have ht := hTail.2
    simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

private lemma rationalPrefixMax_fold (l : List (ℚ×ℕ)) (a : ℚ×ℕ) :
    (l.foldl (fun a b => (max a.1 b.1,a.2+b.2+2)) a).1=(l.map Prod.fst).foldl max a.1 := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => exact ih (max a.1 b.1,a.2+b.2+2)

def countedBinaryOnlineCalibration (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (active : Finset (Fin n)) (fallback : Bool) (j : Fin (J+1))
    (t x : CalibrationBinary) (hist : Fin n → Option Obs) (i : Fin n) (r : PolicyQueryArray n J PSeed) :
    Bool×ℕ :=
  let cap := countedCalibrationEQ x 1
  if fallback || cap.1 then (cap.1,cap.2+2)
  else
    let pos := countedCalibrationLT 0 x
    if !pos.1 then (false,cap.2+pos.2+3)
    else
      let A := active.filter (fun a => a≠i ∧ (hist a).isNone=true)
      let k := onlineQueryRank hist i
      let u := (binaryRemainingHorizon t).evaluate
      let f := fun l : ℕ => estimate A u.1 (z l) (r (k,coefficientIndex J l))
      let q := f 0
      let a := countedBinaryMaxScan q.1 (List.ofFn (fun k : Fin j.val => f (k.val+1)))
      let y := BinaryRational.countedOperation .mul (z j.val) u.1
      let v := BinaryRational.countedOperation .maximum y.1 a.1
      let h := countedCalibrationLE v.1 x
      (h.1,cap.2+pos.2+n*4+u.2+q.2+a.2+y.2+v.2+h.2+12)

theorem countedBinaryOnlineCalibration_value (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (estimateQ : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ×ℕ)
    (he : ∀ A u z s,(estimate A u z s).1.value=(estimateQ A u.value z.value s).1)
    (rows : Fin n → Fin m → ℚ) (active : Finset (Fin n)) (fallback : Bool) (j : Fin (J+1))
    (t x : CalibrationBinary) (hist : Fin n → Option Obs) (i : Fin n) (r : PolicyQueryArray n J PSeed)
    (ha : active.filter (fun a => a≠i ∧ (hist a).isNone=true)=onlineContinuationSet rows hist i) :
    (countedBinaryOnlineCalibration z estimate active fallback j t x hist i r).1 =
      (countedOnlineCalibrationDecision (fun l => (z l).value) estimateQ rows fallback j
        t.value x.value hist i r).1 := by
  let A := onlineContinuationSet rows hist i
  let k := onlineQueryRank hist i
  let f := fun l : ℕ => estimate A (binaryRemainingHorizon t).evaluate.1 (z l) (r (k,coefficientIndex J l))
  let g := fun l : ℕ => estimateQ A (max 0 (min 1 (1-t.value))) (z l).value (r (k,coefficientIndex J l))
  have hg (l : ℕ) : (f l).1.value=(g l).1 := by
    unfold f g
    rw [he,binaryRemainingHorizon_value]
  have hh : (countedBinaryMaxScan (f 0).1 (List.ofFn (fun k : Fin j.val => f (k.val+1)))).1.value =
      (countedPrefixMax g j.val).1 := by
    unfold countedPrefixMax
    rw [countedBinaryMaxScan_value,rationalPrefixMax_fold,hg]
    simp only [List.map_ofFn,Function.comp_def,hg]
  have hrem := binaryRemainingHorizon_value t
  rw [evaluate_value] at hrem
  unfold countedBinaryOnlineCalibration countedOnlineCalibrationDecision
  dsimp only
  rw [ha]
  change (let cap := countedCalibrationEQ x 1
    if fallback || cap.1 then (cap.1,cap.2+2)
    else let pos := countedCalibrationLT 0 x
      if !pos.1 then (false,cap.2+pos.2+3)
      else let a := countedBinaryMaxScan (f 0).1 (List.ofFn (fun k : Fin j.val => f (k.val+1)))
           let y := BinaryRational.countedOperation .mul (z j.val) (binaryRemainingHorizon t).evaluate.1
           let v := BinaryRational.countedOperation .maximum y.1 a.1
           let h := countedCalibrationLE v.1 x
           (h.1,cap.2+pos.2+n*4+(binaryRemainingHorizon t).evaluate.2+(f 0).2+a.2+y.2+v.2+h.2+12)).1=_
  cases fallback <;> by_cases hc : x.value=1 <;> by_cases h0 : x.value≤0 <;>
    simp [BinaryRational.one_value,BinaryRational.zero_value,hc,h0,←not_le,hrem,hh,
      rationalCalibrationOp,g,A,k]

def binaryCalibrationOnlineWork (n J B E W : ℕ) : ℕ :=
  let A := 11*(B+E+1)
  3*calibrationComparisonWork A+n*4+7*workUnit 7 B+
    (J+1)*(W+3600*(E+2)^3+2)+2*(3600*(A+2)^3)+13

theorem countedBinaryOnlineCalibration_work (z : ℕ → CalibrationBinary)
    (estimate : Finset (Fin n) → CalibrationBinary → CalibrationBinary → PSeed → CalibrationBinary×ℕ)
    (active : Finset (Fin n)) (fallback : Bool) (j : Fin (J+1))
    (t x : CalibrationBinary) (hist : Fin n → Option Obs) (i : Fin n) (r : PolicyQueryArray n J PSeed)
    (B E W : ℕ) (ht : RationalHeight t.value B) (hx : RationalHeight x.value B)
    (hz : RationalHeight (z j.val).value B)
    (h : ∀ l,l≤j.val →
      let q := estimate (active.filter (fun a => a≠i ∧ (hist a).isNone=true))
        (binaryRemainingHorizon t).evaluate.1 (z l) (r (onlineQueryRank hist i,coefficientIndex J l))
      RationalHeight q.1.value E ∧ q.2≤W) :
    (countedBinaryOnlineCalibration z estimate active fallback j t x hist i r).2≤
      binaryCalibrationOnlineWork n J B E W := by
  let A := 11*(B+E+1)
  let u := (binaryRemainingHorizon t).evaluate
  let f := fun l : ℕ => estimate (active.filter (fun a => a≠i ∧ (hist a).isNone=true)) u.1 (z l)
    (r (onlineQueryRank hist i,coefficientIndex J l))
  let L := List.ofFn (fun k : Fin j.val => f (k.val+1))
  let a := countedBinaryMaxScan (f 0).1 L
  have h0 := h 0 (Nat.zero_le _)
  have hL : ∀ a∈L,RationalHeight a.1.value E ∧ a.2≤W := by
    intro a ha
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
    exact h (k.val+1) k.isLt
  have ha := countedBinaryMaxScan_bounds (f 0).1 L E W h0.1 hL
  have haW : a.2≤1+j.val*(W+3600*(E+2)^3+2) := by
    simpa only [L,List.length_ofFn] using ha.2
  have hBA : B≤A := by dsimp [A]; omega
  have hEA : E≤A := by dsimp [A]; omega
  have huH : RationalHeight u.1.value (7*(B+1)) := by
    unfold u
    rw [evaluate_value]
    exact (binaryRemainingHorizon t).value_height B (binaryRemainingHorizon_leaves _ _ ht)
  have huW : u.2≤7*workUnit 7 B :=
    (binaryRemainingHorizon t).evaluate_work 7 B (binaryRemainingHorizon_leaves _ _ ht) (by rfl)
  let y := BinaryRational.countedOperation .mul (z j.val) u.1
  let v := BinaryRational.countedOperation .maximum y.1 a.1
  have hyW : y.2≤3600*(A+2)^3 :=
    BinaryRational.countedOperation_work .mul _ _ A (hz.mono hBA) (huH.mono (by dsimp [A]; omega))
  have hyH : RationalHeight y.1.value A := by
    simp only [y,countedCalibrationOp_value,rationalCalibrationOp]
    exact (hz.mul huH).mono (by dsimp [A]; omega)
  have hvW : v.2≤3600*(A+2)^3 :=
    BinaryRational.countedOperation_work .maximum _ _ A hyH (ha.1.mono hEA)
  have hvH : RationalHeight v.1.value A := by
    simp only [v,countedCalibrationOp_value,rationalCalibrationOp]
    exact (hyH.max ha.1).mono (max_le le_rfl hEA)
  have h1 : RationalHeight (1:CalibrationBinary).value A := by
    rw [BinaryRational.one_value]; exact rationalHeight_one.mono (Nat.zero_le _)
  have h0' : RationalHeight (0:CalibrationBinary).value A := by
    rw [BinaryRational.zero_value]; exact rationalHeight_zero.mono (Nat.zero_le _)
  let cap := countedCalibrationEQ x 1
  let pos := countedCalibrationLT 0 x
  let htest := countedCalibrationLE v.1 x
  have hcap : cap.2≤calibrationComparisonWork A := countedCalibrationEQ_work _ _ _ (hx.mono hBA) h1
  have hpos : pos.2≤calibrationComparisonWork A := countedCalibrationLT_work _ _ _ h0' (hx.mono hBA)
  have htestW : htest.2≤calibrationComparisonWork A :=
    countedCalibrationLE_work _ _ _ hvH (hx.mono hBA)
  have hf0 : (f 0).2≤W := h0.2
  have hJ := Nat.mul_le_mul_right (W+3600*(E+2)^3+2) (show j.val+1≤J+1 by omega)
  have hExpand : (j.val+1)*(W+3600*(E+2)^3+2)=
      j.val*(W+3600*(E+2)^3+2)+(W+3600*(E+2)^3+2) := by ring
  rw [hExpand] at hJ
  change (if fallback || cap.1 then (cap.1,cap.2+2)
    else if !pos.1 then (false,cap.2+pos.2+3)
    else (htest.1,cap.2+pos.2+n*4+u.2+(f 0).2+a.2+y.2+v.2+htest.2+12)).2≤_
  change _≤3*calibrationComparisonWork A+n*4+7*workUnit 7 B+
    (J+1)*(W+3600*(E+2)^3+2)+2*(3600*(A+2)^3)+13
  split_ifs <;> dsimp only <;> omega

end ProphetSecretary.Statistics.Calibration
