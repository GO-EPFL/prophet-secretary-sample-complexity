import ProphetSecretary.Statistics.BinaryCalibrationPrimitive
import ProphetSecretary.Statistics.CountedCalibrationPrepare

/-!
# Binary evaluation of the calibration target and interpolation

The target scan keeps a single running minimum, and the knot scan
interpolates only at the first crossing. The work bounds use the
widths of the input arrays and the lengths of the scans.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis
open CalibrationBinaryExpr

private lemma zeroHeight (B : ℕ) : RationalHeight (0:CalibrationBinary).value B := by
  rw [BinaryRational.zero_value]
  exact rationalHeight_zero.mono (Nat.zero_le _)

private lemma oneHeight (B : ℕ) : RationalHeight (1:CalibrationBinary).value B := by
  rw [BinaryRational.one_value]
  exact rationalHeight_one.mono (Nat.zero_le _)

def binaryTargetRatio (M z est invM : CalibrationBinary) : CalibrationBinaryExpr :=
  .node .div (.node .add (.atom est) (.atom invM)) (.node .add (.atom M) (.atom z))

@[simp] lemma binaryTargetRatio_value (M z est invM : CalibrationBinary) :
    (binaryTargetRatio M z est invM).evaluate.1.value=(est.value+invM.value)/(M.value+z.value) := by
  simp only [evaluate_value,binaryTargetRatio,CalibrationBinaryExpr.value,rationalCalibrationOp]

lemma binaryTargetRatio_work (M z est invM : CalibrationBinary) (B : ℕ)
    (hM : RationalHeight M.value B) (hz : RationalHeight z.value B)
    (he : RationalHeight est.value B) (hi : RationalHeight invM.value B) :
    (binaryTargetRatio M z est invM).evaluate.2≤7*workUnit 7 B :=
  (binaryTargetRatio M z est invM).evaluate_work 7 B ⟨⟨he,hi⟩,⟨hM,hz⟩⟩ (by rfl)

lemma binaryTargetRatio_height (M z est invM : CalibrationBinary) (B : ℕ)
    (hM : RationalHeight M.value B) (hz : RationalHeight z.value B)
    (he : RationalHeight est.value B) (hi : RationalHeight invM.value B) :
    RationalHeight (binaryTargetRatio M z est invM).evaluate.1.value (7*(B+1)) := by
  rw [evaluate_value]
  exact (binaryTargetRatio M z est invM).value_height B ⟨⟨he,hi⟩,⟨hM,hz⟩⟩

/-- Each candidate carries the work of its query. The scan adds that
work once, together with one exact binary minimum per candidate. -/
def countedBinaryMinScan (a : CalibrationBinary) : List (CalibrationBinary×ℕ) → CalibrationBinary×ℕ
  | [] => (a,1)
  | b::l =>
    let q := BinaryRational.countedOperation .minimum a b.1
    let p := countedBinaryMinScan q.1 l
    (p.1,b.2+q.2+p.2+2)

lemma countedBinaryMinScan_value (a : CalibrationBinary) (l : List (CalibrationBinary×ℕ)) :
    (countedBinaryMinScan a l).1.value=(l.map (fun b => b.1.value)).foldl min a.value := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih =>
    simpa only [countedBinaryMinScan,List.map_cons,List.foldl_cons,countedCalibrationOp_value,
      rationalCalibrationOp] using ih (BinaryRational.countedOperation .minimum a b.1).1

lemma countedBinaryMinScan_height (a : CalibrationBinary) (l : List (CalibrationBinary×ℕ)) (B : ℕ)
    (ha : RationalHeight a.value B) (hl : ∀ b∈l,RationalHeight b.1.value B) :
    RationalHeight (countedBinaryMinScan a l).1.value B := by
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih =>
    have h := ha.min (hl b List.mem_cons_self)
    rw [max_self] at h
    have hq : RationalHeight (BinaryRational.countedOperation .minimum a b.1).1.value B := by
      rw [countedCalibrationOp_value]
      exact h
    exact ih _ hq (fun c hc => hl c (List.mem_cons_of_mem _ hc))

lemma countedBinaryMinScan_work (a : CalibrationBinary) (l : List (CalibrationBinary×ℕ)) (B W : ℕ)
    (ha : RationalHeight a.value B) (hl : ∀ b∈l,RationalHeight b.1.value B ∧ b.2≤W) :
    (countedBinaryMinScan a l).2≤1+l.length*(W+3600*(B+2)^3+2) := by
  induction l generalizing a with
  | nil => simp [countedBinaryMinScan]
  | cons b l ih =>
    have hb := hl b List.mem_cons_self
    have hqW := BinaryRational.countedOperation_work .minimum a b.1 B ha hb.1
    have hq := ha.min hb.1
    rw [max_self] at hq
    have hq' : RationalHeight (BinaryRational.countedOperation .minimum a b.1).1.value B := by
      rw [countedCalibrationOp_value]
      exact hq
    have hTail := ih _ hq' (fun c hc => hl c (List.mem_cons_of_mem _ hc))
    simp only [countedBinaryMinScan,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

def countedBinaryTargetScan (M invM low high : CalibrationBinary)
    (calls : List (CalibrationBinary×(CalibrationBinary×ℕ))) : CalibrationBinary×ℕ :=
  let vals := calls.map fun c =>
    let r := (binaryTargetRatio M c.1 c.2.1 invM).evaluate
    (r.1,c.2.2+r.2+1)
  let q := countedBinaryMinScan high vals
  let p := BinaryRational.countedOperation .maximum low q.1
  (p.1,q.2+p.2+1)

lemma countedBinaryTargetScan_value (M invM low high : CalibrationBinary)
    (calls : List (CalibrationBinary×(CalibrationBinary×ℕ))) :
    (countedBinaryTargetScan M invM low high calls).1.value =
      max low.value ((calls.map (fun c => (c.2.1.value+invM.value)/(M.value+c.1.value))).foldl min high.value) := by
  simp only [countedBinaryTargetScan,countedCalibrationOp_value,rationalCalibrationOp,
    countedBinaryMinScan_value,List.map_map,Function.comp_def,binaryTargetRatio_value]

def binaryTargetScanWork (len B W : ℕ) : ℕ :=
  let A := 7*(B+1)
  2+len*(W+7*workUnit 7 B+1+3600*(A+2)^3+2)+3600*(A+2)^3

set_option maxHeartbeats 800000 in
theorem countedBinaryTargetScan_work (M invM low high : CalibrationBinary)
    (calls : List (CalibrationBinary×(CalibrationBinary×ℕ))) (B W : ℕ)
    (hM : RationalHeight M.value B) (hi : RationalHeight invM.value B)
    (hlo : RationalHeight low.value B) (hhi : RationalHeight high.value B)
    (h : ∀ c∈calls,RationalHeight c.1.value B ∧ RationalHeight c.2.1.value B ∧ c.2.2≤W) :
    (countedBinaryTargetScan M invM low high calls).2≤binaryTargetScanWork calls.length B W := by
  let A := 7*(B+1)
  have hBA : B≤A := by dsimp [A]; omega
  let f := fun c : CalibrationBinary×(CalibrationBinary×ℕ) =>
    let r := (binaryTargetRatio M c.1 c.2.1 invM).evaluate
    (r.1,c.2.2+r.2+1)
  let vals := calls.map f
  let W' := W+7*workUnit 7 B+1
  have hf : ∀ c∈vals,RationalHeight c.1.value A ∧ c.2≤W' := by
    intro c hc
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hc
    have hh := h x hx
    refine ⟨?_,?_⟩
    · change RationalHeight (binaryTargetRatio M x.1 x.2.1 invM).evaluate.1.value (7*(B+1))
      exact binaryTargetRatio_height M x.1 x.2.1 invM B hM hh.1 hh.2.1 hi
    · have hw := binaryTargetRatio_work M x.1 x.2.1 invM B hM hh.1 hh.2.1 hi
      change x.2.2+(binaryTargetRatio M x.1 x.2.1 invM).evaluate.2+1≤W'
      unfold W'
      omega
  have hmin := countedBinaryMinScan_work high vals A W' (hhi.mono hBA) hf
  have hminH := countedBinaryMinScan_height high vals A (hhi.mono hBA) (fun c hc => (hf c hc).1)
  have hmax := BinaryRational.countedOperation_work .maximum low
    (countedBinaryMinScan high vals).1 A (hlo.mono hBA) hminH
  have hl : vals.length=calls.length := List.length_map _
  rw [hl] at hmin
  change (countedBinaryMinScan high vals).2+
    (BinaryRational.countedOperation .maximum low (countedBinaryMinScan high vals).1).2+1≤_
  change _≤2+calls.length*(W'+3600*(A+2)^3+2)+3600*(A+2)^3
  omega

def binaryDurationSum : List CalibrationBinary → CalibrationBinaryExpr
  | [] => .atom 0
  | x::xs => .node .add (.atom x) (binaryDurationSum xs)

lemma binaryDurationSum_size (xs : List CalibrationBinary) :
    (binaryDurationSum xs).size=2*xs.length+1 := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [binaryDurationSum,size,List.length_cons,ih]; omega

lemma binaryDurationSum_leaves (xs : List CalibrationBinary) (B : ℕ)
    (h : ∀ x∈xs,RationalHeight x.value B) : (binaryDurationSum xs).leavesFit B := by
  induction xs with
  | nil => exact zeroHeight B
  | cons x xs ih => exact ⟨h x List.mem_cons_self,ih (fun y hy => h y (List.mem_cons_of_mem _ hy))⟩

lemma binaryDurationSum_value (xs : List CalibrationBinary) :
    (binaryDurationSum xs).value=(xs.map BinaryRational.value).sum := by
  induction xs with
  | nil => exact BinaryRational.zero_value
  | cons x xs ih => simp only [binaryDurationSum,CalibrationBinaryExpr.value,rationalCalibrationOp,List.map_cons,List.sum_cons,ih]

def binaryDurationKnot (invM : CalibrationBinary) (xs : List CalibrationBinary) : CalibrationBinaryExpr :=
  .node .mul (.atom invM) (binaryDurationSum xs)

@[simp] lemma binaryDurationKnot_value (invM : CalibrationBinary) (xs : List CalibrationBinary) :
    (binaryDurationKnot invM xs).evaluate.1.value=invM.value*(xs.map BinaryRational.value).sum := by
  simp only [evaluate_value,binaryDurationKnot,CalibrationBinaryExpr.value,rationalCalibrationOp,binaryDurationSum_value]

lemma binaryDurationKnot_size (invM : CalibrationBinary) (xs : List CalibrationBinary) :
    (binaryDurationKnot invM xs).size=2*xs.length+3 := by
  simp only [binaryDurationKnot,size,binaryDurationSum_size]
  omega

theorem binaryDurationKnot_work (invM : CalibrationBinary) (xs : List CalibrationBinary) (B : ℕ)
    (hi : RationalHeight invM.value B) (h : ∀ x∈xs,RationalHeight x.value B) :
    (binaryDurationKnot invM xs).evaluate.2≤(2*xs.length+3)*workUnit (2*xs.length+3) B := by
  have hh := (binaryDurationKnot invM xs).evaluate_work (2*xs.length+3) B
    ⟨hi,binaryDurationSum_leaves xs B h⟩ (binaryDurationKnot_size _ _).le
  rwa [binaryDurationKnot_size] at hh

def countedBinaryKnotScan (v : ℕ → CalibrationBinary) (rho : CalibrationBinary) (j : ℕ) :
    ℕ → ℕ × ℕ
  | 0 => (j,1)
  | k+1 =>
    let h := countedCalibrationLE rho (v (j+1))
    if h.1 then (j+1,h.2+4)
    else let q := countedBinaryKnotScan v rho (j+1) k; (q.1,q.2+h.2+4)

lemma countedBinaryKnotScan_value (v : ℕ → CalibrationBinary) (rho : CalibrationBinary) (j k : ℕ) :
    (countedBinaryKnotScan v rho j k).1=(countedKnotScan (fun t => (v t).value) rho.value j k).1 := by
  induction k generalizing j with
  | zero => rfl
  | succ k ih =>
    by_cases h : rho.value≤(v (j+1)).value
    · simp [countedBinaryKnotScan,countedKnotScan,h]
    · simp [countedBinaryKnotScan,countedKnotScan,h,ih]

theorem countedBinaryKnotScan_work (v : ℕ → CalibrationBinary) (rho : CalibrationBinary)
    (j k B : ℕ) (hr : RationalHeight rho.value B) (hv : ∀ i,RationalHeight (v i).value B) :
    (countedBinaryKnotScan v rho j k).2≤1+k*(calibrationComparisonWork B+4) := by
  induction k generalizing j with
  | zero => simp [countedBinaryKnotScan]
  | succ k ih =>
    have hh := countedCalibrationLE_work rho (v (j+1)) B hr (hv _)
    have ht := ih (j+1)
    rw [countedBinaryKnotScan]
    dsimp only
    split_ifs <;> simp only [Nat.add_mul,Nat.one_mul] <;> omega

def binaryInterpolation (rho prev cur : CalibrationBinary) : CalibrationBinaryExpr :=
  .node .div (.node .sub (.atom rho) (.atom prev)) (.node .sub (.atom cur) (.atom prev))

@[simp] lemma binaryInterpolation_value (rho prev cur : CalibrationBinary) :
    (binaryInterpolation rho prev cur).evaluate.1.value=(rho.value-prev.value)/(cur.value-prev.value) := by
  simp only [evaluate_value,binaryInterpolation,CalibrationBinaryExpr.value,rationalCalibrationOp]

theorem binaryInterpolation_work (rho prev cur : CalibrationBinary) (B : ℕ)
    (hr : RationalHeight rho.value B) (hp : RationalHeight prev.value B)
    (hc : RationalHeight cur.value B) :
    (binaryInterpolation rho prev cur).evaluate.2≤7*workUnit 7 B :=
  (binaryInterpolation rho prev cur).evaluate_work 7 B ⟨⟨hr,hp⟩,⟨hc,hp⟩⟩ (by rfl)

end ProphetSecretary.Statistics.Calibration
