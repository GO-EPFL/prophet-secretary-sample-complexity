import ProphetSecretary.Statistics.BinaryCalibrationPublic
import ProphetSecretary.Statistics.FinitePublicScales

/-!
# Public integer scales

The clock, mixture, mark and pilot scales are evaluated on binary
words. The ceiling logarithm is the width of the predecessor, using
saturating subtraction at zero.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

def countedPublicCeilLog (x : List Bool) : List Bool×ℕ :=
  let d := max x.length 1
  let p := countedBinarySubtract d x [true] false
  let q := if p.1.2 then ([],1) else countedTrimBinaryWord p.1.1
  (q.1.length.bits,p.2+q.2+6*(d+1)+3)

lemma countedPublicCeilLog_value (x : List Bool) :
    binaryWordValue (countedPublicCeilLog x).1=Nat.clog 2 (binaryWordValue x) := by
  let d := max x.length 1
  let p := countedBinarySubtract d x [true] false
  have h₀ : [true].length≤d := le_max_right _ _
  have hh := countedBinarySubtract_borrow_iff d x [true] false (le_max_left _ _) h₀
  have hv := countedBinarySubtract_value d x [true] false (le_max_left _ _) h₀
  change binaryWordValue (if p.1.2 then (([] : List Bool),1) else countedTrimBinaryWord p.1.1).1.length.bits=_
  rw [binaryWordValue_bits,calibrationClog_eq_width]
  by_cases h : p.1.2=true
  · have hn : binaryWordValue x<1 := by
      simpa [p,binaryWordValue,bitDigit] using hh.mp h
    simp [h,show binaryWordValue x=0 by omega]
  · have hb : p.1.2=false := Bool.eq_false_iff.mpr h
    have he : binaryWordValue p.1.1=binaryWordValue x-1 := by
      change binaryWordValue x+2^d*bitDigit p.1.2 =
        binaryWordValue [true]+bitDigit false+binaryWordValue p.1.1 at hv
      simp only [hb,bitDigit,Bool.false_eq_true,ite_false,mul_zero,add_zero,
        show binaryWordValue [true]=1 by decide] at hv
      omega
    rw [if_neg h,countedTrimBinaryWord_value,he]

private lemma binaryBits_length_le {a B : ℕ} (h : a<2^B) : a.bits.length≤B := by
  rw [Nat.size_eq_bits_len]
  exact Nat.size_le.mpr h

private lemma binaryClog_le (a : ℕ) : Nat.clog 2 a≤a :=
  Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := a)).le

lemma countedPublicCeilLog_length (x : List Bool) :
    (countedPublicCeilLog x).1.length≤x.length := by
  have h := binaryWordValue_lt_pow x
  have h' := lt_of_le_of_lt (binaryClog_le (binaryWordValue x)) h
  have hv := countedPublicCeilLog_value x
  unfold countedPublicCeilLog at *
  dsimp only at *
  rw [binaryWordValue_bits] at hv
  rw [hv]
  exact binaryBits_length_le h'

lemma countedPublicCeilLog_work (x : List Bool) :
    (countedPublicCeilLog x).2≤25*(x.length+2) := by
  unfold countedPublicCeilLog
  dsimp only
  rw [countedBinarySubtract_work]
  have hd : max x.length 1≤x.length+1 := max_le (by omega) (by omega)
  split_ifs
  · dsimp only
    omega
  · rw [countedTrimBinaryWord_work,countedBinarySubtract_length]
    omega

inductive PublicNaturalExpression
  | literal (n : ℕ)
  | add (a b : PublicNaturalExpression)
  | mul (a b : PublicNaturalExpression)
  | ceilLog (a : PublicNaturalExpression)

namespace PublicNaturalExpression

def value : PublicNaturalExpression → ℕ
  | .literal n => n
  | .add a b => a.value+b.value
  | .mul a b => a.value*b.value
  | .ceilLog a => Nat.clog 2 a.value

def size : PublicNaturalExpression → ℕ
  | .literal _ => 1
  | .add a b | .mul a b => a.size+b.size+1
  | .ceilLog a => a.size+1

def leavesFit (B : ℕ) : PublicNaturalExpression → Prop
  | .literal n => n.bits.length≤B
  | .add a b | .mul a b => a.leavesFit B ∧ b.leavesFit B
  | .ceilLog a => a.leavesFit B

def evaluate : PublicNaturalExpression → List Bool×ℕ
  | .literal n => (n.bits,3*n.bits.length+3)
  | .add a b =>
    let x := a.evaluate
    let y := b.evaluate
    let q := countedBinaryAdd (max x.1.length y.1.length) x.1 y.1 false
    (q.1,x.2+y.2+q.2+3)
  | .mul a b =>
    let x := a.evaluate
    let y := b.evaluate
    let q := countedBinaryMultiply x.1 y.1
    let t := countedTrimBinaryWord q.1
    (t.1,x.2+y.2+q.2+t.2+3)
  | .ceilLog a =>
    let x := a.evaluate
    let q := countedPublicCeilLog x.1
    (q.1,x.2+q.2+2)

@[simp] lemma evaluate_value (e : PublicNaturalExpression) :
    binaryWordValue e.evaluate.1=e.value := by
  induction e with
  | literal n => exact binaryWordValue_bits n
  | add a b ha hb =>
    simp only [evaluate,value,countedBinaryAdd_value _ _ _ _ (le_max_left _ _) (le_max_right _ _),
      bitDigit,Bool.false_eq_true,ite_false,add_zero,ha,hb]
  | mul a b ha hb =>
    simp only [evaluate,value,countedTrimBinaryWord_value,binaryWordValue_bits,
      countedBinaryMultiply_value,ha,hb]
  | ceilLog a ha =>
    simp only [evaluate,value,countedPublicCeilLog_value,ha]

lemma evaluate_length (e : PublicNaturalExpression) (B : ℕ) (h : e.leavesFit B) :
    e.evaluate.1.length≤e.size*(B+1) := by
  induction e with
  | literal n =>
    change n.bits.length≤B at h
    simp only [evaluate,size,one_mul]
    omega
  | add a b ha hb =>
    have hA := ha h.1
    have hB := hb h.2
    have hh := countedBinaryAdd_length (max a.evaluate.1.length b.evaluate.1.length)
      a.evaluate.1 b.evaluate.1 false
    change _≤(a.size+b.size+1)*(B+1)
    rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
    change (countedBinaryAdd _ a.evaluate.1 b.evaluate.1 false).1.length≤_
    omega
  | mul a b ha hb =>
    have hA := ha h.1
    have hB := hb h.2
    simp only [evaluate,countedTrimBinaryWord_value,countedBinaryMultiply_value,size]
    apply binaryBits_length_le
    rw [Nat.add_mul,Nat.add_mul,Nat.one_mul,pow_add,pow_add]
    have hh := Nat.mul_lt_mul_of_lt_of_lt (binaryWordValue_lt_pow a.evaluate.1)
      (binaryWordValue_lt_pow b.evaluate.1)
    have hh' := hh.trans_le (Nat.mul_le_mul
      (Nat.pow_le_pow_right (by decide) hA) (Nat.pow_le_pow_right (by decide) hB))
    exact hh'.trans_le (Nat.le_mul_of_pos_right _ (by positivity))
  | ceilLog a ha =>
    change a.leavesFit B at h
    apply (countedPublicCeilLog_length _).trans ((ha h).trans _)
    exact Nat.mul_le_mul_right _ (by simp [size])

def workUnit (L B : ℕ) : ℕ := 200*(L*(B+1)+3)^2

theorem evaluate_work (e : PublicNaturalExpression) (L B : ℕ)
    (h : e.leavesFit B) (he : e.size≤L) :
    e.evaluate.2≤e.size*workUnit L B := by
  let W := L*(B+1)
  have hW : 0<W+3 := by omega
  have hUnit : workUnit L B=200*(W+3)^2 := rfl
  induction e with
  | literal n =>
    change n.bits.length≤B at h
    have hL : 1≤L := he
    have hw : B+1≤W := by
      exact Nat.le_mul_of_pos_left _ hL
    have hp : W+3≤(W+3)^2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hW (by decide : 1≤2)
    change 3*n.bits.length+3≤1*(200*(W+3)^2)
    omega
  | add a b ha hb =>
    change a.leavesFit B ∧ b.leavesFit B at h
    have hA : a.size≤L := by simp only [size] at he; omega
    have hB : b.size≤L := by simp only [size] at he; omega
    have hLA := (evaluate_length a B h.1).trans (Nat.mul_le_mul_right (B+1) hA)
    have hLB := (evaluate_length b B h.2).trans (Nat.mul_le_mul_right (B+1) hB)
    have hw := max_le hLA hLB
    have hp : W+3≤(W+3)^2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hW (by decide : 1≤2)
    have hAw := ha h.1 hA
    have hBw := hb h.2 hB
    change _≤(a.size+b.size+1)*workUnit L B
    rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
    change a.evaluate.2+b.evaluate.2+(countedBinaryAdd _ a.evaluate.1 b.evaluate.1 false).2+3≤_
    rw [countedBinaryAdd_work]
    change max a.evaluate.1.length b.evaluate.1.length≤W at hw
    rw [hUnit] at hAw hBw ⊢
    omega
  | mul a b ha hb =>
    change a.leavesFit B ∧ b.leavesFit B at h
    have hA : a.size≤L := by simp only [size] at he; omega
    have hB : b.size≤L := by simp only [size] at he; omega
    have hLA : a.evaluate.1.length≤W := (evaluate_length a B h.1).trans (Nat.mul_le_mul_right (B+1) hA)
    have hLB : b.evaluate.1.length≤W := (evaluate_length b B h.2).trans (Nat.mul_le_mul_right (B+1) hB)
    let q := countedBinaryMultiply a.evaluate.1 b.evaluate.1
    have hQ : q.2≤96*(W+3)^2 := by
      have hmul := Nat.mul_le_mul (show a.evaluate.1.length+1≤W+3 by omega)
        (show 2*a.evaluate.1.length+b.evaluate.1.length+2≤3*(W+3) by omega)
      have hEq : 32*((W+3)*(3*(W+3)))=96*(W+3)^2 := by ring
      exact (countedBinaryMultiply_work _ _).trans (by
        rw [Nat.mul_assoc]
        exact (Nat.mul_le_mul_left 32 hmul).trans_eq hEq)
    have ht := countedTrimBinaryWord_work q.1
    have hl : q.1.length≤3*W :=
      (countedBinaryMultiply_length _ _).trans (by omega)
    have hp : W+3≤(W+3)^2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hW (by decide : 1≤2)
    have hAw := ha h.1 hA
    have hBw := hb h.2 hB
    change _≤(a.size+b.size+1)*workUnit L B
    rw [Nat.add_mul,Nat.add_mul,Nat.one_mul]
    change a.evaluate.2+b.evaluate.2+q.2+(countedTrimBinaryWord q.1).2+3≤_
    rw [hUnit] at hAw hBw ⊢
    omega
  | ceilLog a ha =>
    change a.leavesFit B at h
    have hA : a.size≤L := by simp only [size] at he; omega
    have hLA : a.evaluate.1.length≤W := (evaluate_length a B h).trans (Nat.mul_le_mul_right (B+1) hA)
    have hQ := countedPublicCeilLog_work a.evaluate.1
    have hp : W+3≤(W+3)^2 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hW (by decide : 1≤2)
    have hAw := ha h hA
    change _≤(a.size+1)*workUnit L B
    rw [Nat.add_mul,Nat.one_mul]
    change a.evaluate.2+(countedPublicCeilLog a.evaluate.1).2+2≤_
    rw [hUnit] at hAw ⊢
    omega

def run (e : PublicNaturalExpression) : ℕ×ℕ :=
  let q := e.evaluate
  (binaryWordValue q.1,q.2+3*q.1.length+3)

@[simp] lemma run_value (e : PublicNaturalExpression) : e.run.1=e.value := e.evaluate_value

lemma run_work (e : PublicNaturalExpression) (L B : ℕ) (h : e.leavesFit B) (he : e.size≤L) :
    e.run.2≤L*workUnit L B+3*(L*(B+1))+3 := by
  have hw := (e.evaluate_work L B h he).trans (Nat.mul_le_mul_right _ he)
  have hl := (e.evaluate_length B h).trans (Nat.mul_le_mul_right _ he)
  change e.evaluate.2+3*e.evaluate.1.length+3≤_
  omega

end PublicNaturalExpression

namespace PublicNaturalExpression

local notation "ℓ" => literal
local infixl:65 " +ₑ " => add
local infixl:70 " *ₑ " => mul

private def pilotRankExpr (m : ℕ) : PublicNaturalExpression := ℓ 12 *ₑ ceilLog (ℓ 2 *ₑ ℓ m)
private def pilotRoundsExpr (m : ℕ) : PublicNaturalExpression := ℓ 500 *ₑ pilotRankExpr m
private def sampleBudgetExpr (m : ℕ) : PublicNaturalExpression := ℓ 3 *ₑ ℓ m +ₑ pilotRoundsExpr m
private def markSlotsExpr (n m : ℕ) : PublicNaturalExpression := ℓ n *ₑ (sampleBudgetExpr m +ₑ ℓ 1)
private def coinDemandExpr (m : ℕ) : PublicNaturalExpression := ℓ m *ₑ ℓ m

private def clockBitsExpr (n m zInv : ℕ) : PublicNaturalExpression :=
  let N := ℓ n +ₑ ℓ 1
  let M := ℓ m +ₑ ℓ 1
  ceilLog (ℓ m *ₑ ℓ m *ₑ ℓ m *ₑ (N *ₑ N) +ₑ
    ℓ 392 *ₑ ℓ zInv *ₑ (M *ₑ M *ₑ M) +ₑ ℓ 20 +ₑ ℓ m)

private def publicIntegerExpr (n m zInv : ℕ) (i : Fin 7) : PublicNaturalExpression :=
  match i.val with
  | 0 => clockBitsExpr n m zInv
  | 1 => ceilLog (coinDemandExpr m)
  | 2 => ceilLog (coinDemandExpr m *ₑ (markSlotsExpr n m *ₑ markSlotsExpr n m))
  | 3 => pilotRankExpr m
  | 4 => pilotRoundsExpr m
  | 5 => sampleBudgetExpr m
  | _ => markSlotsExpr n m

private theorem publicIntegerExpr_size (n m zInv : ℕ) (i : Fin 7) :
    (publicIntegerExpr n m zInv i).size≤100 := by
  fin_cases i <;>
    norm_num [publicIntegerExpr,clockBitsExpr,coinDemandExpr,markSlotsExpr,sampleBudgetExpr,
      pilotRoundsExpr,pilotRankExpr,size]

private theorem publicIntegerExpr_leaves (n m zInv : ℕ) (i : Fin 7) :
    (publicIntegerExpr n m zInv i).leavesFit (n+m+zInv+500) := by
  let B := n+m+zInv+500
  have hl (a : ℕ) (ha : a≤B) : a.bits.length≤B :=
    binaryBits_length_le ((Nat.lt_two_pow_self (n := a)).trans_le (Nat.pow_le_pow_right (by decide) ha))
  fin_cases i <;>
    simp only [publicIntegerExpr,clockBitsExpr,coinDemandExpr,markSlotsExpr,sampleBudgetExpr,pilotRoundsExpr,
      pilotRankExpr,leavesFit] <;>
    (repeat' apply And.intro) <;> apply hl <;> dsimp [B] <;> omega

end PublicNaturalExpression

open PublicNaturalExpression

structure BinaryPublicIntegerScales where
  clockBits : ℕ
  coinBits : ℕ
  markBits : ℕ
  pilotRank : ℕ
  pilotRounds : ℕ
  sampleBudget : ℕ
  markSlots : ℕ
  work : ℕ

def countedBinaryPublicIntegers (n m zInv : ℕ) : BinaryPublicIntegerScales :=
  let q := Vector.ofFn (fun i : Fin 7 => (publicIntegerExpr n m zInv i).run)
  ⟨(q.get 0).1,(q.get 1).1,(q.get 2).1,(q.get 3).1,(q.get 4).1,(q.get 5).1,(q.get 6).1,
    (∑ i : Fin 7,(q.get i).2)+10⟩

theorem countedBinaryPublicIntegers_value (n m zInv : ℕ) :
    let q := countedBinaryPublicIntegers n m zInv
    q.clockBits=calibrationClockBits n m zInv ∧ q.coinBits=Nat.clog 2 (m^2) ∧
      q.markBits=outerMarkBits n m ∧ q.pilotRank=outerPilotRank m ∧
      q.pilotRounds=outerPilotRounds m ∧ q.sampleBudget=outerSampleBudget m ∧
      q.markSlots=outerMarkSlotCount n m := by
  simp only [countedBinaryPublicIntegers,calibrationVectorGet_ofFn,run_value]
  refine ⟨?_,?_,?_,rfl,rfl,?_,?_⟩
  · change Nat.clog 2 (m*m*m*((n+1)*(n+1))+392*zInv*((m+1)*(m+1)*(m+1))+20+m)=
      Nat.clog 2 (m^3*(n+1)^2+392*zInv*(m+1)^3+20+m)
    congr 1
    ring
  · change Nat.clog 2 (m*m)=Nat.clog 2 (m^2)
    rw [pow_two]
  · change Nat.clog 2 (m*m*((n*(3*m+500*(12*Nat.clog 2 (2*m))+1))*
      (n*(3*m+500*(12*Nat.clog 2 (2*m))+1))))=outerMarkBits n m
    unfold outerMarkBits
    congr 1
    ring
  · rw [outerSampleBudget_eq]
    change 3*m+500*(12*Nat.clog 2 (2*m))=3*m+6000*Nat.clog 2 (2*m)
    omega
  · change n*(3*m+500*(12*Nat.clog 2 (2*m))+1)=outerMarkSlotCount n m
    unfold outerMarkSlotCount outerPilotRounds outerPilotRank
    ring

def binaryPublicIntegersWork (n m zInv : ℕ) : ℕ :=
  let B := n+m+zInv+500
  7*(100*PublicNaturalExpression.workUnit 100 B+3*(100*(B+1))+3)+10

theorem countedBinaryPublicIntegers_work (n m zInv : ℕ) :
    (countedBinaryPublicIntegers n m zInv).work≤binaryPublicIntegersWork n m zInv := by
  let B := n+m+zInv+500
  let W := 100*PublicNaturalExpression.workUnit 100 B+3*(100*(B+1))+3
  have h (i : Fin 7) : (publicIntegerExpr n m zInv i).run.2≤W :=
    (publicIntegerExpr n m zInv i).run_work 100 B (publicIntegerExpr_leaves n m zInv i)
      (publicIntegerExpr_size n m zInv i)
  have hh : (∑ i : Fin 7,(publicIntegerExpr n m zInv i).run.2)≤7*W := by
    have hs := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => h i)
    simpa only [Finset.sum_const,Fintype.card_fin,Finset.card_univ,nsmul_eq_mul,Nat.cast_id] using hs
  unfold countedBinaryPublicIntegers
  simp only [calibrationVectorGet_ofFn]
  exact Nat.add_le_add_right hh 10

set_option maxRecDepth 2048 in
/-- The public integer setup has a quadratic work bound with an
explicit coefficient depending only on the fixed inverse scale. -/
theorem binaryPublicIntegersWork_polynomial (n m zInv : ℕ) :
    binaryPublicIntegersWork n m zInv≤1000000000000*(zInv+501)^2*(n+m+2)^2 := by
  let X := (zInv+501)*(n+m+2)
  let B := n+m+zInv+500
  have hx : 1≤X := Nat.succ_le_of_lt (by dsimp [X]; positivity)
  have hBX : B+1≤X := by
    dsimp [B,X]
    nlinarith only [Nat.zero_le (zInv*(n+m)),Nat.zero_le zInv,Nat.zero_le n,Nat.zero_le m]
  have hT : 100*(B+1)+3≤103*X := by omega
  have hPow := Nat.pow_le_pow_left hT 2
  have hPow' : (100*(B+1)+3)^2≤10609*X^2 := hPow.trans_eq (by ring)
  have hXsq : X≤X^2 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<X) (by decide : 1≤2)
  change 7*(100*(200*(100*(B+1)+3)^2)+3*(100*(B+1))+3)+10≤_
  have hPoly : 1000000000000*(zInv+501)^2*(n+m+2)^2=1000000000000*X^2 := by dsimp [X]; ring
  rw [hPoly]
  nlinarith only [hPow',hBX,hXsq,hx]

end ProphetSecretary.Statistics.Calibration
