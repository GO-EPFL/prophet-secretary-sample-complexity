import ProphetSecretary.Analysis.ArithmeticExpressionBits
import ProphetSecretary.Statistics.PlannerPrimitiveHeight

/-!
# The empirical excess scan on binary fractions

The scan compares each stored observation with zero, accumulates the positive
parts, and divides by the positive-observation count. Its intermediate
fractions use the same rational values as the scalar planner's row scan.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

def countedBinaryExcessTotals (v : BinaryFraction) : List BinaryFraction →
    (BinaryFraction × BinaryFraction) × ℕ
  | [] => ((BinaryFraction.ofInt 0,BinaryFraction.ofInt 0),1)
  | x::l =>
    let q := countedBinaryExcessTotals v l
    let test := x.countedLE (BinaryFraction.ofInt 0)
    if test.1 then (q.1,q.2+test.2+4) else
      let d := x.countedSub v
      let a := BinaryFraction.Operation.maximum.countedEval (BinaryFraction.ofInt 0) d.1
      let s := a.1.countedAdd q.1.1
      let c := q.1.2.countedAdd (BinaryFraction.ofInt 1)
      ((s.1,c.1),q.2+test.2+d.2+a.2+s.2+c.2+12)

private lemma ofInt_positive_den (z : ℤ) : 0 < binaryWordValue (BinaryFraction.ofInt z).denominator :=
  (show 0 < binaryWordValue [true] by decide)

theorem countedBinaryExcessTotals_correct (v : BinaryFraction) (l : List BinaryFraction)
    (hv : 0 < binaryWordValue v.denominator) (hl : ∀ x ∈ l, 0 < binaryWordValue x.denominator) :
    let q := (countedBinaryExcessTotals v l).1
    let r := (countedPlannerExcessTotals v.value (l.map BinaryFraction.value)).1
    q.1.value = r.1 ∧ q.2.value = r.2 ∧
      0 < binaryWordValue q.1.denominator ∧ 0 < binaryWordValue q.2.denominator := by
  induction l with
  | nil => exact ⟨BinaryFraction.ofInt_value 0,BinaryFraction.ofInt_value 0,ofInt_positive_den _,ofInt_positive_den _⟩
  | cons x l ih =>
    let q := (countedBinaryExcessTotals v l).1
    let r := (countedPlannerExcessTotals v.value (l.map BinaryFraction.value)).1
    have ht := ih (fun y hy => hl y (List.mem_cons_of_mem _ hy))
    have hx := hl x List.mem_cons_self
    let z := BinaryFraction.ofInt 0
    let one := BinaryFraction.ofInt 1
    have hz : z.value = 0 := BinaryFraction.ofInt_value 0
    have hone : one.value = 1 := BinaryFraction.ofInt_value 1
    let t := x.countedLE z
    have htst : t.1 = true ↔ x.value ≤ 0 := by
      rw [← hz]
      exact BinaryFraction.countedLE_correct x z hx (ofInt_positive_den 0)
    by_cases ht' : t.1 = true
    · have hneg : ¬0 < x.value := not_lt.mpr (htst.mp ht')
      rw [countedBinaryExcessTotals,if_pos (show (x.countedLE z).1 = true from ht')]
      simpa only [List.map_cons,countedPlannerExcessTotals,if_neg hneg] using ht
    · have hpos : 0 < x.value := lt_of_not_ge (mt htst.mpr ht')
      let d := x.countedSub v
      let a := BinaryFraction.Operation.maximum.countedEval z d.1
      let s := a.1.countedAdd q.1
      let c := q.2.countedAdd one
      have hd := BinaryFraction.countedSub_correct x v hx hv
      have ha := BinaryFraction.Operation.countedEval_correct .maximum z d.1 (ofInt_positive_den 0) hd.2
      have hs := BinaryFraction.countedAdd_correct a.1 q.1 ha.2 ht.2.2.1
      have hC := BinaryFraction.countedAdd_correct q.2 one ht.2.2.2 (ofInt_positive_den 1)
      rw [countedBinaryExcessTotals,if_neg (show ¬(x.countedLE z).1 = true from ht')]
      simp only [List.map_cons,countedPlannerExcessTotals,if_pos hpos]
      refine ⟨?_,?_,hs.2,hC.2⟩
      · change s.1.value = max 0 (x.value-v.value)+r.1
        rw [hs.1,ha.1,show d.1.value = _ from hd.1,show q.1.value = r.1 from ht.1]
        exact congrArg (fun t => max t (x.value-v.value)+r.1) hz
      · change c.1.value = r.2+1
        rw [hC.1,show q.2.value = r.2 from ht.2.1,hone]

def countedBinaryEmpiricalExcess (l : List BinaryFraction) (v : BinaryFraction) : BinaryFraction × ℕ :=
  let t := countedBinaryExcessTotals v l
  let q := t.1.1.countedDiv t.1.2
  (q.1,t.2+q.2+3)

theorem countedBinaryEmpiricalExcess_correct (l : List BinaryFraction) (v : BinaryFraction)
    (hv : 0 < binaryWordValue v.denominator) (hl : ∀ x ∈ l, 0 < binaryWordValue x.denominator) :
    (countedBinaryEmpiricalExcess l v).1.value =
      (countedPlannerExcess (l.map BinaryFraction.value) v.value).1 ∧
      0 < binaryWordValue (countedBinaryEmpiricalExcess l v).1.denominator := by
  let t := (countedBinaryExcessTotals v l).1
  let q := t.1.countedDiv t.2
  have h := countedBinaryExcessTotals_correct v l hv hl
  have hq := BinaryFraction.countedDiv_correct t.1 t.2 h.2.2.1 h.2.2.2
  refine ⟨hq.1.trans ?_,hq.2⟩
  rw [show t.1.value = _ from h.1,show t.2.value = _ from h.2.1]
  rfl

def binaryExcessOperandWidth (m Y A P : ℕ) : ℕ := m*(Y+1)+P+A+Y+4

private lemma binaryExcess_nativeHeights (l : List BinaryFraction) (v : BinaryFraction)
    (m Y A P : ℕ) (hm : l.length ≤ m) (hP : m ≤ 2^P)
    (hv : RationalHeight v.value A) (hY : ∀ x ∈ l, RationalHeight x.value Y) :
    let q := (countedPlannerExcessTotals v.value (l.map BinaryFraction.value)).1
    RationalHeight q.1 (m*(Y+1)+P+A+1) ∧ RationalHeight q.2 P := by
  let row := l.map BinaryFraction.value
  have hlen : row.length ≤ m := by simpa [row] using hm
  obtain ⟨a,c,he,ha,hc⟩ := countedPlannerExcessTotals_affine row v.value Y (by
    intro y hy
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hy
    exact hY x hx)
  have hC := rationalHeight_natCast c P (hc.trans (hlen.trans hP))
  have hL := Nat.mul_le_mul_right (Y+1) hlen
  refine ⟨?_,?_⟩
  · change RationalHeight (countedPlannerExcessTotals v.value row).1.1 _
    rw [he]
    exact (ha.sub (hC.mul hv)).mono (by omega)
  · change RationalHeight (countedPlannerExcessTotals v.value row).1.2 _
    rw [countedPlannerExcessTotals_value]
    exact rationalHeight_natCast _ _ (List.countP_le_length.trans (hlen.trans hP))

theorem countedBinaryExcessTotals_width_work (l : List BinaryFraction) (v : BinaryFraction)
    (m Y A P : ℕ) (hm : l.length ≤ m) (hP : m ≤ 2^P)
    (hv : 0 < binaryWordValue v.denominator) (hvB : v.width ≤ A+1) (hvA : RationalHeight v.value A)
    (hY : ∀ x ∈ l, 0 < binaryWordValue x.denominator ∧ x.width ≤ Y+1 ∧ RationalHeight x.value Y) :
    let q := countedBinaryExcessTotals v l
    let B := binaryExcessOperandWidth m Y A P
    q.1.1.width ≤ B ∧ q.1.2.width ≤ B ∧
      q.2 ≤ 1+l.length*(5*(3500*(B+1)^3)+12) := by
  let B := binaryExcessOperandWidth m Y A P
  let C := 3500*(B+1)^3
  have hB : 1 ≤ B := by dsimp [B,binaryExcessOperandWidth]; omega
  have hvW : v.width ≤ B := hvB.trans (by dsimp [B,binaryExcessOperandWidth]; omega)
  change (countedBinaryExcessTotals v l).1.1.width ≤ B ∧
    (countedBinaryExcessTotals v l).1.2.width ≤ B ∧
    (countedBinaryExcessTotals v l).2 ≤ 1+l.length*(5*C+12)
  induction l with
  | nil =>
    exact ⟨hB,hB,by simp [countedBinaryExcessTotals]⟩
  | cons x l ih =>
    let q := countedBinaryExcessTotals v l
    let z := BinaryFraction.ofInt 0
    let one := BinaryFraction.ofInt 1
    let t := x.countedLE z
    have hm' : l.length ≤ m := (Nat.le_succ _).trans hm
    have hT (y : BinaryFraction) (hy : y ∈ l) := hY y (List.mem_cons_of_mem _ hy)
    have h := ih hm' hT
    have hx := hY x List.mem_cons_self
    have hxW : x.width ≤ B := hx.2.1.trans (by dsimp [B,binaryExcessOperandWidth]; omega)
    have hzW : z.width ≤ B := hB
    have hoW : one.width ≤ B := hB
    have ht : t.2 ≤ C := (BinaryFraction.countedLE_work x z B hxW hzW hx.1 (ofInt_positive_den 0)).trans
      (Nat.mul_le_mul_right _ (by decide))
    by_cases he : t.1 = true
    · rw [countedBinaryExcessTotals,if_pos (show (x.countedLE z).1 = true from he)]
      refine ⟨h.1,h.2.1,?_⟩
      change q.2+t.2+4 ≤ _
      have hq : q.2 ≤ 1+l.length*(5*C+12) := h.2.2
      rw [List.length_cons,Nat.add_mul,Nat.one_mul]
      omega
    · let d := x.countedSub v
      let a := BinaryFraction.Operation.maximum.countedEval z d.1
      let s := a.1.countedAdd q.1.1
      let c := q.1.2.countedAdd one
      have hd := BinaryFraction.countedSub_correct x v hx.1 hv
      have ha := BinaryFraction.Operation.countedEval_correct .maximum z d.1 (ofInt_positive_den 0) hd.2
      have hD : d.1.width ≤ B := (BinaryFraction.countedSub_width x v hx.1 hv _ (hx.2.2.sub hvA)).trans
        (by dsimp [B,binaryExcessOperandWidth]; omega)
      have haW : a.1.width ≤ B := by
        change (if (z.countedLE d.1).1 then d.1 else z).width ≤ B
        split_ifs <;> assumption
      have ht' := countedBinaryExcessTotals_correct v l hv (fun y hy => (hT y hy).1)
      have hN := binaryExcess_nativeHeights (x::l) v m Y A P hm hP hvA (fun y hy => (hY y hy).2.2)
      have hV := countedBinaryExcessTotals_correct v (x::l) hv (fun y hy => (hY y hy).1)
      rw [countedBinaryExcessTotals,if_neg (show ¬(x.countedLE z).1 = true from he)] at hV ⊢
      have hS : RationalHeight (a.1.value+q.1.1.value) (B-1) := by
        rw [← (BinaryFraction.countedAdd_correct a.1 q.1.1 ha.2 ht'.2.2.1).1]
        change RationalHeight s.1.value _
        rw [show s.1.value = _ from hV.1]
        exact hN.1.mono (by dsimp [B,binaryExcessOperandWidth]; omega)
      have hCount : RationalHeight (q.1.2.value+one.value) (B-1) := by
        rw [← (BinaryFraction.countedAdd_correct q.1.2 one ht'.2.2.2 (ofInt_positive_den 1)).1]
        change RationalHeight c.1.value _
        rw [show c.1.value = _ from hV.2.1]
        exact hN.2.mono (by dsimp [B,binaryExcessOperandWidth]; omega)
      refine ⟨?_,?_,?_⟩
      · exact (BinaryFraction.countedAdd_width a.1 q.1.1 ha.2 ht'.2.2.1 (B-1) hS).trans
          (Nat.sub_add_cancel hB).le
      · exact (BinaryFraction.countedAdd_width q.1.2 one ht'.2.2.2 (ofInt_positive_den 1) (B-1) hCount).trans
          (Nat.sub_add_cancel hB).le
      · have hdC : d.2 ≤ C := (BinaryFraction.countedSub_work x v B hxW hvW).trans
          (Nat.mul_le_mul_right _ (by decide))
        have haC : a.2 ≤ C := BinaryFraction.Operation.countedEval_work .maximum z d.1
          (ofInt_positive_den 0) hd.2 B hB hzW hD
        have hsC : s.2 ≤ C := (BinaryFraction.countedAdd_work a.1 q.1.1 B haW h.1).trans
          (Nat.mul_le_mul_right _ (by decide))
        have hcC : c.2 ≤ C := (BinaryFraction.countedAdd_work q.1.2 one B h.2.1 hoW).trans
          (Nat.mul_le_mul_right _ (by decide))
        change q.2+t.2+d.2+a.2+s.2+c.2+12 ≤ _
        have hq : q.2 ≤ 1+l.length*(5*C+12) := h.2.2
        rw [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega

theorem countedBinaryEmpiricalExcess_work (l : List BinaryFraction) (v : BinaryFraction)
    (m Y A P : ℕ) (hm : l.length ≤ m) (hP : m ≤ 2^P)
    (hv : 0 < binaryWordValue v.denominator) (hvB : v.width ≤ A+1) (hvA : RationalHeight v.value A)
    (hY : ∀ x ∈ l, 0 < binaryWordValue x.denominator ∧ x.width ≤ Y+1 ∧ RationalHeight x.value Y) :
    let B := binaryExcessOperandWidth m Y A P
    (countedBinaryEmpiricalExcess l v).2 ≤ 4+l.length*(5*(3500*(B+1)^3)+12)+3300*(B+1)^3 := by
  let B := binaryExcessOperandWidth m Y A P
  have hB : 1 ≤ B := by dsimp [B,binaryExcessOperandWidth]; omega
  have h := countedBinaryExcessTotals_width_work l v m Y A P hm hP hv hvB hvA hY
  have he := BinaryFraction.countedDiv_work (countedBinaryExcessTotals v l).1.1
    (countedBinaryExcessTotals v l).1.2 B hB h.1 h.2.1
  change (countedBinaryExcessTotals v l).2+_+3 ≤
    4+l.length*(5*(3500*(B+1)^3)+12)+3300*(B+1)^3
  have ht : (countedBinaryExcessTotals v l).2 ≤ 1+l.length*(5*(3500*(B+1)^3)+12) := h.2.2
  omega

end ProphetSecretary.Statistics
