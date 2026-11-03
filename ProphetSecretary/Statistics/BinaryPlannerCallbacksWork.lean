import ProphetSecretary.Statistics.BinaryPlannerCallbacks

/-!
# Bounds for the binary planner callbacks

Frame arithmetic uses only the input horizon, duration weight, and the
weight product. The excess scan has additive height growth in its argument.
All work bounds hold on every raw transition and every admissible row size.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {n : ℕ}

private lemma operationValue (op : BinaryFraction.Operation) (x y : BinaryRational) :
    (BinaryRational.countedOperation op x y).1.value=op.eval x.value y.value := by
  change (op.countedEval x.storage y.storage).1.normalizeSign.value = _
  rw [BinaryFraction.normalizeSign_value]
  exact (BinaryFraction.Operation.countedEval_correct op _ _ (BinaryRational.storage_denominator_pos x)
    (BinaryRational.storage_denominator_pos y)).1

private lemma binaryZeroHeight (B : ℕ) : RationalHeight (0:BinaryRational).value B := by
  rw [BinaryRational.zero_value]
  exact rationalHeight_zero.mono (Nat.zero_le _)

private lemma binaryOneHeight (B : ℕ) : RationalHeight (1:BinaryRational).value B := by
  rw [BinaryRational.one_value]
  exact rationalHeight_one.mono (Nat.zero_le _)

private lemma binaryFourHeight (B : ℕ) (h : 2≤B) : RationalHeight (4:BinaryRational).value B := by
  rw [show (4:BinaryRational).value=(4:ℚ) from BinaryRational.ofRat_value 4]
  exact rationalHeight_four.mono h

private lemma binaryClampHeight (lo hi x : BinaryRational) (B : ℕ)
    (hlo : RationalHeight lo.value B) (hhi : RationalHeight hi.value B) (hx : RationalHeight x.value B) :
    RationalHeight (countedBinaryClamp lo hi x).1.value B := by
  rw [countedBinaryClamp_value,BinaryRational.max_value,BinaryRational.min_value]
  exact (hlo.max ((hhi.min hx).mono (max_le le_rfl le_rfl))).mono (max_le le_rfl le_rfl)

def binaryFrameWorkBound (n P U Z : ℕ) : ℕ :=
  let W := n*(P+3)
  let B := U+Z+2*W+P+10
  (1+n*(3400*(P+2)^3+5))+(1+n*(3*(3600*(W+P+5)^3)+5))+9*(3600*(B+2)^3)+24

theorem countedBinaryPlannerFrame_work (p : Fin n → BinaryRational) (x : ScalarPlannerListState n BinaryRational)
    (P U Z : ℕ) (hx : x.1.Nodup) (hp : ∀ i, RationalHeight (p i).value P)
    (hu : RationalHeight x.2.1.value U) (hz : RationalHeight x.2.2.value Z) (hZ : 2≤Z) :
    (countedBinaryPlannerFrame p x).2≤binaryFrameWorkBound n P U Z := by
  let W := n*(P+3)
  let B := U+Z+2*W+P+10
  let C := 3600*(B+2)^3
  let A := countedBinaryPlannerActive p x.1
  let w := countedBinaryPlannerWeight p A.1
  let u := countedBinaryClamp 0 1 x.2.1
  let z := countedBinaryClamp 0 4 x.2.2
  let a := BinaryRational.countedOperation .mul z.1 u.1
  let o := BinaryRational.countedOperation .div a.1 w.1
  let s := BinaryRational.countedOperation .sub w.1 1
  let t := BinaryRational.countedOperation .mul 4 w.1
  let c := BinaryRational.countedOperation .div s.1 t.1
  have hL : x.1.length≤n := by
    simpa only [List.toFinset_card_of_nodup hx,Fintype.card_fin] using Finset.card_le_univ x.1.toFinset
  have hA : A.1.length≤n := by
    rw [countedBinaryPlannerActive_value]
    exact (countedPlannerActive_length p x.1).trans hL
  have hAw : A.2≤1+n*(3400*(P+2)^3+5) := (countedBinaryPlannerActive_work p x.1 P hp).trans
    (Nat.add_le_add_left (Nat.mul_le_mul_right _ hL) 1)
  have hw : w.2≤1+n*(3*(3600*(W+P+5)^3)+5) := by
    have h := countedBinaryPlannerWeight_work p A.1 P n hp hA
    exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hA) 1)
  have hWH : RationalHeight w.1.value W := (countedBinaryPlannerWeight_height p A.1 P hp).mono
    (Nat.mul_le_mul_right _ hA)
  have hu' : RationalHeight u.1.value U := binaryClampHeight _ _ _ U (binaryZeroHeight U) (binaryOneHeight U) hu
  have hz' : RationalHeight z.1.value Z := binaryClampHeight _ _ _ Z (binaryZeroHeight Z) (binaryFourHeight Z hZ) hz
  have huB : U≤B := by dsimp [B]; omega
  have hzB : Z≤B := by dsimp [B]; omega
  have hwB : W≤B := by dsimp [B]; omega
  have h4B : 2≤B := by dsimp [B]; omega
  have huW : u.2≤2*C+2 := countedBinaryClamp_work _ _ _ B (binaryZeroHeight B) (binaryOneHeight B) (hu.mono huB)
  have hzW : z.2≤2*C+2 := countedBinaryClamp_work _ _ _ B (binaryZeroHeight B) (binaryFourHeight B h4B) (hz.mono hzB)
  have ha : RationalHeight a.1.value B := by
    rw [operationValue]
    exact (hz'.mul hu').mono (by dsimp [B]; omega)
  have hs : RationalHeight s.1.value B := by
    rw [operationValue]
    exact (hWH.sub (binaryOneHeight 0)).mono (by dsimp [B]; omega)
  have ht : RationalHeight t.1.value B := by
    rw [operationValue]
    exact ((binaryFourHeight 2 le_rfl).mul hWH).mono (by dsimp [B]; omega)
  have haW : a.2≤C := BinaryRational.countedOperation_work .mul _ _ B (hz'.mono hzB) (hu'.mono huB)
  have hoW : o.2≤C := BinaryRational.countedOperation_work .div _ _ B ha (hWH.mono hwB)
  have hsW : s.2≤C := BinaryRational.countedOperation_work .sub _ _ B (hWH.mono hwB) (binaryOneHeight B)
  have htW : t.2≤C := BinaryRational.countedOperation_work .mul _ _ B (binaryFourHeight B h4B) (hWH.mono hwB)
  have hcW : c.2≤C := BinaryRational.countedOperation_work .div _ _ B hs ht
  change A.2+w.2+u.2+z.2+a.2+o.2+s.2+t.2+c.2+20≤_
  change _≤(1+n*(3400*(P+2)^3+5))+(1+n*(3*(3600*(W+P+5)^3)+5))+9*C+24
  omega

theorem countedBinaryPlannerChild_work (q : ScalarPlannerFrame n BinaryRational)
    (s : PlannerListOutput n BinaryRational) (B : ℕ)
    (hu : RationalHeight q.time.value B) (hs : RationalHeight s.2.1.value B) :
    (countedBinaryPlannerChild q s).2≤3*(3600*(B+2)^3)+8 := by
  let f := countedBinaryClamp 0 1 s.2.1
  let u := BinaryRational.countedOperation .mul q.time f.1
  have hf : f.2≤2*(3600*(B+2)^3)+2 := countedBinaryClamp_work _ _ _ B (binaryZeroHeight B) (binaryOneHeight B) hs
  have h := BinaryRational.countedOperation_work .mul q.time f.1 B hu
    (binaryClampHeight _ _ _ B (binaryZeroHeight B) (binaryOneHeight B) hs)
  change f.2+u.2+6≤_
  have h' : u.2≤3600*(B+2)^3 := h
  omega

def binaryPayoffWorkBound (n m P M Y A : ℕ) : ℕ :=
  let W := n*(P+3)
  let V := W+A
  let E := m*(Y+1)+2*M+V+1
  let S := binaryExcessOperandWidth m Y V M
  let B := E+W+A
  (1+n*(3400*(P+2)^3+5))+(1+n*(3*(3600*(W+P+5)^3)+5)) +
    2*(3600*(B+2)^3) + (4+m*(5*(3500*(S+1)^3)+12)+3300*(S+1)^3) +
    100*(E+2)^3+4*m+10

theorem countedBinaryPlannerPayoff_work (rows : Vector (List BinaryRational) n) (p : Fin n → BinaryRational)
    (s : PlannerListOutput n BinaryRational) (a : BinaryRational) (m P M Y A : ℕ)
    (hRows : ∀ i, (rows.get i).length≤m) (hm : m≤2^M)
    (hy : ∀ i x, x∈rows.get i → RationalHeight x.value Y) (hp : ∀ i, RationalHeight (p i).value P)
    (hs : s.2.2.Nodup) (ha : RationalHeight a.value A) :
    (countedBinaryPlannerPayoff rows p s a).2≤binaryPayoffWorkBound n m P M Y A := by
  cases hI : s.1 with
  | none => simp only [countedBinaryPlannerPayoff,hI]; dsimp only [binaryPayoffWorkBound]; omega
  | some i =>
    let W := n*(P+3)
    let V := W+A
    let E := m*(Y+1)+2*M+V+1
    let S := binaryExcessOperandWidth m Y V M
    let B := E+W+A
    let C := 3600*(B+2)^3
    let l := countedBinaryPlannerActive p s.2.2
    let w := countedBinaryPlannerWeight p l.1
    let v := BinaryRational.countedOperation .mul w.1 a
    let row := (rows.get i).map BinaryRational.storage
    let e := countedBinaryEmpiricalExcess row v.1.storage
    have hD (x : BinaryFraction) (hx : x∈row) : 0<binaryWordValue x.denominator ∧ x.width≤Y+1 ∧ RationalHeight x.value Y := by
      obtain ⟨y,hy',rfl⟩ := List.mem_map.mp hx
      exact ⟨BinaryRational.storage_denominator_pos y,BinaryRational.storage_width y Y (hy i y hy'),hy i y hy'⟩
    have hE := countedBinaryEmpiricalExcess_correct row v.1.storage (BinaryRational.storage_denominator_pos v.1)
      (fun x hx => (hD x hx).1)
    let d := BinaryRational.ofFraction e.1 hE.2
    let z := BinaryRational.countedOperation .div d w.1
    have hL : s.2.2.length≤n := by
      simpa only [List.toFinset_card_of_nodup hs,Fintype.card_fin] using Finset.card_le_univ s.2.2.toFinset
    have hA : l.1.length≤n := by
      rw [countedBinaryPlannerActive_value]
      exact (countedPlannerActive_length p s.2.2).trans hL
    have hl : l.2≤1+n*(3400*(P+2)^3+5) := (countedBinaryPlannerActive_work p s.2.2 P hp).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_right _ hL) 1)
    have hw : w.2≤1+n*(3*(3600*(W+P+5)^3)+5) := by
      have h := countedBinaryPlannerWeight_work p l.1 P n hp hA
      exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hA) 1)
    have hW : RationalHeight w.1.value W := (countedBinaryPlannerWeight_height p l.1 P hp).mono
      (Nat.mul_le_mul_right _ hA)
    have hV : RationalHeight v.1.value V := by rw [operationValue]; exact hW.mul ha
    have hRow : row.length≤m := by simpa only [row,List.length_map] using hRows i
    have heW : e.2≤4+m*(5*(3500*(S+1)^3)+12)+3300*(S+1)^3 := by
      have h := countedBinaryEmpiricalExcess_work row v.1.storage m Y V M hRow hm
        (BinaryRational.storage_denominator_pos _) (BinaryRational.storage_width _ V hV) hV hD
      have h' := Nat.mul_le_mul_right (5*(3500*(S+1)^3)+12) hRow
      exact h.trans (by change 4+row.length*(5*(3500*(S+1)^3)+12)+3300*(S+1)^3≤_; omega)
    have hEH : RationalHeight e.1.value E := by
      rw [show e.1.value=(countedPlannerExcess (row.map BinaryFraction.value) v.1.storage.value).1 from hE.1]
      exact countedPlannerExcess_height _ _ Y M V m (by
        intro x hx
        obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hx
        exact (hD u hu).2.2) (by simpa only [List.length_map] using hRow) hm hV
    have hEW : e.1.width≤E+1 := by
      let q := (countedBinaryExcessTotals v.1.storage row).1
      have hq := countedBinaryExcessTotals_correct v.1.storage row
        (BinaryRational.storage_denominator_pos v.1) (fun x hx => (hD x hx).1)
      have hd := BinaryFraction.countedDiv_correct q.1 q.2 hq.2.2.1 hq.2.2.2
      change (q.1.countedDiv q.2).1.width≤_
      apply BinaryFraction.countedDiv_width q.1 q.2 hq.2.2.1 hq.2.2.2 E
      rw [← hd.1]
      exact hEH
    have hRed : e.1.countedReduce.2≤100*(E+2)^3 := (BinaryFraction.countedReduce_work e.1).trans
      (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hEW 1) 3))
    have hd : RationalHeight d.value E := by rw [show d.value=e.1.value from BinaryRational.ofFraction_value _ _]; exact hEH
    have hvW : v.2≤C := BinaryRational.countedOperation_work .mul _ _ B
      (hW.mono (by dsimp [B]; omega)) (ha.mono (by dsimp [B]; omega))
    have hzW : z.2≤C := BinaryRational.countedOperation_work .div _ _ B
      (hd.mono (by dsimp [B]; omega)) (hW.mono (by dsimp [B]; omega))
    simp only [countedBinaryPlannerPayoff,hI]
    change l.2+w.2+v.2+e.2+e.1.countedReduce.2+z.2+4*row.length+10≤_
    change _≤(1+n*(3400*(P+2)^3+5))+(1+n*(3*(3600*(W+P+5)^3)+5))+2*C+
      (4+m*(5*(3500*(S+1)^3)+12)+3300*(S+1)^3)+100*(E+2)^3+4*m+10
    omega

end ProphetSecretary.Statistics
