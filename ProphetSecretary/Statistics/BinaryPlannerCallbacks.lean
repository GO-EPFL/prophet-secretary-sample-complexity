import ProphetSecretary.Statistics.BinaryPlannerWeights
import ProphetSecretary.Statistics.BinaryPlannerSamplerWork
import ProphetSecretary.Statistics.BinaryEmpiricalExcess

/-!
# Counted binary callbacks for the empirical recursion

The frame, child, and excess callbacks use the binary field primitives.
The transition uses the counted binary subset sampler. The stored values
agree with the native planner callbacks before and after decoding.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

variable {n : ℕ}

def countedBinaryClamp (lo hi x : BinaryRational) : BinaryRational × ℕ :=
  let a := BinaryRational.countedOperation .minimum hi x
  let b := BinaryRational.countedOperation .maximum lo a.1
  (b.1,a.2+b.2+2)

lemma countedBinaryClamp_value (lo hi x : BinaryRational) :
    (countedBinaryClamp lo hi x).1=max lo (min hi x) := by
  simp only [countedBinaryClamp,BinaryRational.countedOperation_value,BinaryRational.applyOperation]

lemma countedBinaryClamp_work (lo hi x : BinaryRational) (B : ℕ)
    (hlo : RationalHeight lo.value B) (hhi : RationalHeight hi.value B) (hx : RationalHeight x.value B) :
    (countedBinaryClamp lo hi x).2≤2*(3600*(B+2)^3)+2 := by
  let a := BinaryRational.countedOperation .minimum hi x
  let b := BinaryRational.countedOperation .maximum lo a.1
  have ha : RationalHeight a.1.value B := by
    rw [BinaryRational.countedOperation_value]
    change RationalHeight (min hi x).value B
    rw [BinaryRational.min_value]
    exact (hhi.min hx).mono (max_le le_rfl le_rfl)
  have h₁ := BinaryRational.countedOperation_work .minimum hi x B hhi hx
  have h₂ := BinaryRational.countedOperation_work .maximum lo a.1 B hlo ha
  change a.2+b.2+2≤_
  exact (Nat.add_le_add_right (Nat.add_le_add h₁ h₂) 2).trans_eq (by ring)

def countedBinaryPlannerFrame (p : Fin n → BinaryRational) (x : ScalarPlannerListState n BinaryRational) :
    ScalarPlannerFrame n BinaryRational × ℕ :=
  let A := countedBinaryPlannerActive p x.1
  let w := countedBinaryPlannerWeight p A.1
  let u := countedBinaryClamp 0 1 x.2.1
  let z := countedBinaryClamp 0 4 x.2.2
  let a := BinaryRational.countedOperation .mul z.1 u.1
  let o := BinaryRational.countedOperation .div a.1 w.1
  let s := BinaryRational.countedOperation .sub w.1 1
  let t := BinaryRational.countedOperation .mul 4 w.1
  let c := BinaryRational.countedOperation .div s.1 t.1
  (⟨A.1,u.1,z.1,w.1,a.1,o.1,c.1⟩,A.2+w.2+u.2+z.2+a.2+o.2+s.2+t.2+c.2+20)

lemma countedBinaryPlannerFrame_value (p : Fin n → BinaryRational) (x : ScalarPlannerListState n BinaryRational) :
    (countedBinaryPlannerFrame p x).1=(countedScalarPlannerFrame p x).1 := by
  simp only [countedBinaryPlannerFrame,countedScalarPlannerFrame,countedBinaryPlannerActive_value,
    countedBinaryPlannerWeight_value,countedBinaryClamp_value,BinaryRational.countedOperation_value,BinaryRational.applyOperation]

def countedBinaryPlannerChild (q : ScalarPlannerFrame n BinaryRational)
    (s : PlannerListOutput n BinaryRational) : ScalarPlannerListState n BinaryRational × ℕ :=
  let f := countedBinaryClamp 0 1 s.2.1
  let u := BinaryRational.countedOperation .mul q.time f.1
  ((s.2.2,u.1,q.durationWeight),f.2+u.2+6)

lemma countedBinaryPlannerChild_value (q : ScalarPlannerFrame n BinaryRational)
    (s : PlannerListOutput n BinaryRational) :
    (countedBinaryPlannerChild q s).1=(countedScalarPlannerChild q s).1 := by
  simp only [countedBinaryPlannerChild,countedScalarPlannerChild,countedBinaryClamp_value,
    BinaryRational.countedOperation_value,BinaryRational.applyOperation]

def countedBinaryPlannerPayoff (rows : Vector (List BinaryRational) n) (p : Fin n → BinaryRational)
    (s : PlannerListOutput n BinaryRational) (a : BinaryRational) : BinaryRational × ℕ :=
  match s.1 with
  | none => (0,1)
  | some i =>
    let A := countedBinaryPlannerActive p s.2.2
    let w := countedBinaryPlannerWeight p A.1
    let v := BinaryRational.countedOperation .mul w.1 a
    let row := (rows.get i).map BinaryRational.storage
    let e := countedBinaryEmpiricalExcess row v.1.storage
    have hE := (countedBinaryEmpiricalExcess_correct row v.1.storage
      (BinaryRational.storage_denominator_pos v.1) (by
        intro q hq
        obtain ⟨x,_,rfl⟩ := List.mem_map.mp hq
        exact BinaryRational.storage_denominator_pos x)).2
    let d := BinaryRational.ofFraction e.1 hE
    let z := BinaryRational.countedOperation .div d w.1
    (z.1,A.2+w.2+v.2+e.2+e.1.countedReduce.2+z.2+4*row.length+10)

lemma countedBinaryPlannerPayoff_value (rows : Vector (List BinaryRational) n) (p : Fin n → BinaryRational)
    (s : PlannerListOutput n BinaryRational) (a : BinaryRational) :
    (countedBinaryPlannerPayoff rows p s a).1=(countedScalarPlannerPayoff rows p s a).1 := by
  apply BinaryRational.value_injective
  have h := countedScalarPlannerPayoff_valueMap BinaryRational.valueHom BinaryRational.value_strictMono rows p s a
  change (countedBinaryPlannerPayoff rows p s a).1.value=BinaryRational.valueHom (countedScalarPlannerPayoff rows p s a).1
  rw [← h]
  rcases s with ⟨o,t,l⟩
  cases o with
  | none => simp [countedBinaryPlannerPayoff,countedScalarPlannerPayoff,plannerListOutputMap,BinaryRational.zero_value]
  | some i =>
    let A := (countedBinaryPlannerActive p l).1
    let w := (countedBinaryPlannerWeight p A).1
    let v := (BinaryRational.countedOperation .mul w a).1
    let row := (rows.get i).map BinaryRational.storage
    let e := countedBinaryEmpiricalExcess row v.storage
    have he := countedBinaryEmpiricalExcess_correct row v.storage (BinaryRational.storage_denominator_pos v)
      (fun q hq => by obtain ⟨x,_,rfl⟩ := List.mem_map.mp hq; exact BinaryRational.storage_denominator_pos x)
    let d := BinaryRational.ofFraction e.1 he.2
    have hD : d.value=(countedPlannerExcess ((rows.get i).map BinaryRational.value) v.value).1 := by
      rw [show d.value=e.1.value from BinaryRational.ofFraction_value _ _,he.1,List.map_map]
      rfl
    have hw : w.value=(countedPlannerWeight (fun j => (p j).value)
        (countedPlannerActive (fun j => (p j).value) l).1).1 := by
      dsimp only [w,A]
      rw [countedBinaryPlannerWeight_value,countedBinaryPlannerActive_value]
      change BinaryRational.valueHom _ = (countedPlannerWeight (fun i => BinaryRational.valueHom (p i))
        (countedPlannerActive (fun i => BinaryRational.valueHom (p i)) l).1).1
      rw [countedPlannerActive_valueMap BinaryRational.valueHom BinaryRational.value_strictMono,
        countedPlannerWeight_valueMap]
    have hV : v.value=w.value*a.value := by
      rw [show v=(BinaryRational.countedOperation .mul w a).1 from rfl,BinaryRational.countedOperation_value]
      exact BinaryRational.mul_value w a
    change (BinaryRational.countedOperation .div d w).1.value =
      (countedScalarPlannerPayoff (plannerRowsValueMap BinaryRational.value rows) (fun j => (p j).value)
        (some i,t.value,l) a.value).1
    rw [BinaryRational.countedOperation_value]
    change (BinaryRational.div d w).value = _
    rw [BinaryRational.div_value,hD,hV,hw]
    have hr : (plannerRowsValueMap BinaryRational.value rows).get i = (rows.get i).map BinaryRational.value := by
      simp [plannerRowsValueMap,Vector.get]
    simp only [countedScalarPlannerPayoff,hr]

end ProphetSecretary.Statistics
