import ProphetSecretary.Statistics.BinaryPlannerSampler
import ProphetSecretary.Statistics.PlannerPrimitiveHeight

/-!
# Hard work of the binary planner transition

Both categorical scans use polynomial-size prefix expressions. Each
Bernoulli test compares already bounded words, and all active lists have
length at most the instance size.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

def samplerExpressionSize (n : ℕ) : ℕ := 100*(n+1)^3
def samplerLiteralHeight (n B : ℕ) : ℕ := B+n+2
def binarySamplerUnit (n B : ℕ) : ℕ :=
  let W := samplerExpressionSize n
  let B' := samplerLiteralHeight n B
  let D := (B'+1)*W+1
  binaryPrefixScanUnit B' W W+100*(D+1)^3+2*n+10

def binarySamplerWorkBound (n B : ℕ) : ℕ :=
  let C := binarySamplerUnit n B
  (1+2*n)+(1+n*C)+(1+n*(C+3))+(1+2*n)+(1+n*C)+C+(1+n*(C+3))+(1+3*n)+(1+2*n)+10

private lemma sampler_n_le_pow (n B : ℕ) : n≤2^samplerLiteralHeight n B :=
  (show n<2^n from Nat.lt_two_pow_self).le.trans (Nat.pow_le_pow_right (by decide) (by unfold samplerLiteralHeight; omega))

private lemma sampler_size_pos (n : ℕ) : 0<samplerExpressionSize n := by unfold samplerExpressionSize; positivity

private lemma firstPrefix_caps {n : ℕ} (l : List (Fin n)) (hL : l.length≤n) (B : ℕ) (i : Fin n) :
    LiteralsBounded (samplerLiteralHeight n B) (countedPlannerFirstPrefix l i).1 ∧
      (countedPlannerFirstPrefix l i).1.work≤samplerExpressionSize n ∧
      (countedPlannerFirstPrefix l i).2≤samplerExpressionSize n := by
  have h := work_plannerFirstPrefixExpression_le l i
  have hG := countedPlannerFirstPrefix_work l i
  have hM := Nat.mul_le_mul hL (Nat.add_le_add_left (Nat.mul_le_mul_left 24 hL) 16)
  have h2 := Nat.pow_le_pow_left hL 2
  refine ⟨?_,?_,?_⟩
  · rw [countedPlannerFirstPrefix_value]
    exact (plannerFirstPrefixExpression_literals l i).mono (by unfold samplerLiteralHeight; omega)
  · rw [countedPlannerFirstPrefix_value]
    exact h.trans (by unfold samplerExpressionSize; nlinarith [Nat.zero_le (n^3)])
  · exact hG.trans (by unfold samplerExpressionSize; nlinarith [Nat.zero_le (n^3)])

private lemma uniformPrefix_caps {n : ℕ} (l : List (Fin n)) (hL : l.length≤n) (B : ℕ) (i : Fin n) :
    LiteralsBounded (samplerLiteralHeight n B) (countedPlannerUniformPrefix l i).1 ∧
      (countedPlannerUniformPrefix l i).1.work≤samplerExpressionSize n ∧
      (countedPlannerUniformPrefix l i).2≤samplerExpressionSize n := by
  refine ⟨?_,?_,?_⟩
  · rw [countedPlannerUniformPrefix_value]
    apply literalsBounded_sumList
    intro j _
    exact ⟨Nat.succ_le_of_lt (by positivity),hL.trans (sampler_n_le_pow n B)⟩
  · exact (countedPlannerUniformPrefix_expression_work l i).trans (by unfold samplerExpressionSize; nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3)])
  · exact (countedPlannerUniformPrefix_generation_work l i).trans (by unfold samplerExpressionSize; nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3)])

private lemma binaryPrefixWork_to_unit (n B : ℕ) :
    binaryPrefixScanUnit (samplerLiteralHeight n B) (samplerExpressionSize n) (samplerExpressionSize n) ≤
      binarySamplerUnit n B := by dsimp only [binarySamplerUnit]; omega

private lemma binaryFirstCoinTest_work {n : ℕ} (p : Fin n → BinaryRational) (k : Fin n)
    (u : Fin n → BinaryRational) (i : Fin n) (B : ℕ)
    (hp : ∀ i, RationalHeight (p i).value B) (hu : RationalHeight (u i).value B) :
    (binaryFirstCoinTest p k u i).2≤binarySamplerUnit n B := by
  let W := samplerExpressionSize n
  let B' := samplerLiteralHeight n B
  let D := (B'+1)*W+1
  let e := plannerProbabilityExpression i
  let v := countedBinaryEval (fun j => (p j).storage) e
  have hp' (j : Fin n) : RationalHeight (p j).value B' := (hp j).mono (by unfold B' samplerLiteralHeight; omega)
  have hx (j : Fin n) : 0<binaryWordValue (p j).storage.denominator ∧ (p j).storage.width≤B'+1 ∧
      RationalHeight (p j).storage.value B' :=
    ⟨BinaryRational.storage_denominator_pos _,BinaryRational.storage_width _ B' (hp' j),hp' j⟩
  have he := (plannerProbabilityExpression_literals i).mono (show 2≤B' by unfold B' samplerLiteralHeight; omega)
  have hW : e.work≤W := by
    simp only [e,work_plannerProbabilityExpression,W,samplerExpressionSize]
    exact (by decide : (9:ℕ)≤100).trans (Nat.le_mul_of_pos_right _ (by positivity))
  have h := countedBinaryEval_correct (fun j => (p j).storage) B' hx e he
  have hV : v.1.width≤D := h.2.2.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hW) 1)
  have hU : (u i).storage.width≤D := (BinaryRational.storage_width _ B hu).trans (by
    have h' : B'+1≤(B'+1)*W := Nat.le_mul_of_pos_right (B'+1) (sampler_size_pos n)
    have h'' : B+1≤B'+1 := by dsimp only [B',samplerLiteralHeight]; omega
    exact h''.trans (h'.trans (Nat.le_succ _)))
  have hC := BinaryFraction.countedLE_work (u i).storage v.1 D hU hV
    (BinaryRational.storage_denominator_pos _) h.2.1
  have hE : v.2≤W*(3500*((B'+1)*W+2)^3) := binaryExpression_work_le (fun j => (p j).storage) B' W hx e he hW
  unfold binaryFirstCoinTest
  split_ifs
  · change v.2+((u i).storage.countedLE v.1).2+3≤_
    have hc : ((u i).storage.countedLE v.1).2≤3400*((B'+1)*W+2)^3 := hC
    unfold binarySamplerUnit binaryPrefixScanUnit
    change _≤W+W*(3500*((B'+1)*W+2)^3)+3400*((B'+1)*W+2)^3+5+100*(D+1)^3+2*n+10
    omega
  · change (1:ℕ)≤_
    dsimp only [binarySamplerUnit]
    omega

private lemma binaryFraction_work {n : ℕ} (l : List (Fin n)) (hL : l.length≤n)
    (u : Fin n → BinaryRational) (B : ℕ) (hu : ∀ i, RationalHeight (u i).value B) :
    (countedBinaryPlannerFraction l u).2≤binarySamplerUnit n B := by
  let W := samplerExpressionSize n
  let B' := samplerLiteralHeight n B
  let D := (B'+1)*W+1
  let q := countedMaximumExpression l (fun j => (.input j,1))
  let e := ArithmeticExpression.minimum q.1 (.integer 1)
  let v := countedBinaryEval (fun j => (u j).storage) e
  have hU (i : Fin n) : RationalHeight (u i).value B' := (hu i).mono (by unfold B' samplerLiteralHeight; omega)
  have hx (i : Fin n) : 0<binaryWordValue (u i).storage.denominator ∧ (u i).storage.width≤B'+1 ∧
      RationalHeight (u i).storage.value B' :=
    ⟨BinaryRational.storage_denominator_pos _,BinaryRational.storage_width _ B' (hU i),hU i⟩
  have he : LiteralsBounded B' e := by
    change LiteralsBounded B' q.1 ∧ 1≤2^B'
    refine ⟨?_,Nat.succ_le_of_lt (by positivity)⟩
    rw [countedMaximumExpression_value]
    exact literalsBounded_maximumList _ _ _ (fun _ _ => trivial)
  have hw : e.work≤W := by
    change q.1.work+1+1≤W
    have h := work_maximumList_le l (fun i => ArithmeticExpression.input i) 1 (fun _ _ => le_rfl)
    rw [show q.1 = maximumList l (fun i => ArithmeticExpression.input i) from countedMaximumExpression_value _ _]
    unfold W samplerExpressionSize
    nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3)]
  have hg : q.2≤W := by
    have h := countedMaximumExpression_work l (fun i : Fin n => (.input i,1)) 1 (fun _ _ => le_rfl)
    unfold W samplerExpressionSize
    change q.2≤1+l.length*(1+2) at h
    nlinarith [Nat.zero_le (n^2),Nat.zero_le (n^3)]
  have h := countedBinaryEval_correct (fun j => (u j).storage) B' hx e he
  have hv : v.1.width≤D := h.2.2.1.trans (Nat.add_le_add_right (Nat.mul_le_mul_left _ hw) 1)
  have hr := (BinaryFraction.countedReduce_work v.1).trans
    (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hv 1) 3))
  have hE : v.2≤W*(3500*((B'+1)*W+2)^3) := binaryExpression_work_le (fun j => (u j).storage) B' W hx e he hw
  change q.2+v.2+v.1.countedReduce.2+5≤_
  unfold binarySamplerUnit binaryPrefixScanUnit
  change _≤W+W*(3500*((B'+1)*W+2)^3)+3400*((B'+1)*W+2)^3+5+100*(D+1)^3+2*n+10
  omega

private lemma binaryTailCoinTest_work {n : ℕ} (D : List (Fin n)) (hD : D.length≤n)
    (s : BinaryRational) (u : Fin n → BinaryRational) (i : Fin n) (B : ℕ)
    (hs : RationalHeight s.value B) (hu : RationalHeight (u i).value B) :
    (binaryTailCoinTest D s u i).2≤binarySamplerUnit n B := by
  let W := samplerExpressionSize n
  let B' := samplerLiteralHeight n B
  let V := (B'+1)*W+1
  have hV : B+1≤V := by
    have h' : B'+1≤(B'+1)*W := Nat.le_mul_of_pos_right (B'+1) (sampler_size_pos n)
    have h'' : B+1≤B'+1 := by dsimp only [B',samplerLiteralHeight]; omega
    exact h''.trans (h'.trans (Nat.le_succ _))
  have hc := BinaryFraction.countedLE_work (u i).storage s.storage V
    ((BinaryRational.storage_width _ B hu).trans hV) ((BinaryRational.storage_width _ B hs).trans hV)
    (BinaryRational.storage_denominator_pos _) (BinaryRational.storage_denominator_pos s)
  have hm := (countedListContains_work i D).trans (show 1+2*D.length≤1+2*n by omega)
  unfold binaryTailCoinTest
  dsimp only
  unfold binarySamplerUnit binaryPrefixScanUnit
  change _≤W+W*(3500*((B'+1)*W+2)^3)+3400*((B'+1)*W+2)^3+5+100*(V+1)^3+2*n+10
  change ((u i).storage.countedLE s.storage).2≤3400*((B'+1)*W+2)^3 at hc
  split_ifs <;> dsimp only <;> omega

theorem countedBinaryUniformSampler_work {n : ℕ} (l : List (Fin n)) (hl : l.Nodup)
    (p : Fin n → BinaryRational) (s : PlannerFieldSeed n BinaryRational) (B : ℕ)
    (hp : ∀ i, RationalHeight (p i).value B)
    (hs : RationalHeight s.1.1.value B ∧ (∀ i, RationalHeight (s.1.2 i).value B) ∧
      RationalHeight s.2.1.value B ∧ (∀ i, RationalHeight (s.2.2.1 i).value B) ∧
        ∀ i, RationalHeight (s.2.2.2 i).value B) :
    (countedBinaryUniformSampler l p s).2≤binarySamplerWorkBound n B := by
  have hLen : l.length≤n := by
    have h := Finset.card_le_univ l.toFinset
    simpa only [List.toFinset_card_of_nodup hl,Fintype.card_fin] using h
  cases l with
  | nil => change 1≤_; dsimp only [binarySamplerWorkBound]; omega
  | cons a l =>
    let L := a::l
    let C := binarySamplerUnit n B
    let B' := samplerLiteralHeight n B
    let W := samplerExpressionSize n
    let ma := countedMaximumScan a L
    let first := countedBinaryMinimumScan (countedPlannerFirstPrefix L) p s.1.1 ma.1 L
    let coins := countedBinaryFilter (binaryFirstCoinTest p first.1 s.1.2) L
    let D := first.1::coins.1
    let md := countedMaximumScan first.1 D
    let q := countedBinaryMinimumScan (countedPlannerUniformPrefix D) (fun _ => BinaryRational.ofRat 0) s.2.1 md.1 D
    let f := countedBinaryPlannerFraction D s.2.2.1
    let tail := countedBinaryFilter (binaryTailCoinTest D f.1 s.2.2.2) L
    let comp := countedPredicateFilter (fun j => j≠q.1) D
    let out := countedAppend comp.1 tail.1
    have hD : D.length≤n := by
      let A := countedPlannerFirstStage L a (fun i => (p i).value) (s.1.1.value,fun i => (s.1.2 i).value)
      have he : D=A.1.2 := by
        simp only [D,coins,first,A,countedPlannerFirstStage,countedBinaryMinimumScan_value,
          countedPlannerFirstChoice,ma,countedBinaryFilter_value,binaryFirstCoinTest_value,countedPlannerFirstCoins_value]
      rw [he]
      exact (countedPlannerFirstStage_invariants L hl a List.mem_cons_self _ _).2.2.trans hLen
    have hBB : B≤B' := by unfold B' samplerLiteralHeight; omega
    have hFirst := countedBinaryMinimumScan_work (countedPlannerFirstPrefix L) p s.1.1 ma.1 L B' W W
      (Nat.succ_le_of_lt (sampler_size_pos n)) (fun i => (hp i).mono hBB) (hs.1.mono hBB)
      (fun i _ => firstPrefix_caps L hLen B i)
    have hFirst' : first.2≤1+n*C := hFirst.trans
      (Nat.add_le_add_left (Nat.mul_le_mul hLen (binaryPrefixWork_to_unit n B)) 1)
    have hCoins' : coins.2≤1+n*(C+3) :=
      (countedBinaryFilter_work _ L C (fun i _ => binaryFirstCoinTest_work p first.1 s.1.2 i B hp (hs.2.1 i))).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ hLen) 1)
    have hId := countedBinaryMinimumScan_work (countedPlannerUniformPrefix D) (fun _ => BinaryRational.ofRat 0)
      s.2.1 md.1 D B' W W (Nat.succ_le_of_lt (sampler_size_pos n))
      (fun _ => by rw [BinaryRational.ofRat_value]; exact rationalHeight_zero.mono (Nat.zero_le _))
      (hs.2.2.1.mono hBB) (fun i _ => uniformPrefix_caps D hD B i)
    have hId' : q.2≤1+n*C := hId.trans
      (Nat.add_le_add_left (Nat.mul_le_mul hD (binaryPrefixWork_to_unit n B)) 1)
    have hF : f.2≤C := binaryFraction_work D hD s.2.2.1 B hs.2.2.2.1
    have hFH : RationalHeight f.1.value B := by
      rw [countedBinaryPlannerFraction_value]
      exact countedPlannerFraction_height D _ B hs.2.2.2.1
    have hTail : tail.2≤1+n*(C+3) :=
      (countedBinaryFilter_work _ L C (fun i _ => binaryTailCoinTest_work D hD f.1 s.2.2.2 i B hFH (hs.2.2.2.2 i))).trans
        (Nat.add_le_add_left (Nat.mul_le_mul_right _ hLen) 1)
    have hL' : L.length≤n := hLen
    have hMa : ma.2≤1+2*n := (countedMaximumScan_work a L).le.trans (by omega)
    have hMd : md.2≤1+2*n := (countedMaximumScan_work first.1 D).le.trans (by omega)
    have hComp : comp.2≤1+3*n := (countedPredicateFilter_work (fun j => j≠q.1) D).trans (by omega)
    have hCL : comp.1.length≤n := by
      rw [countedPredicateFilter_value]
      exact (List.length_filter_le _ _).trans hD
    have hOut : out.2≤1+2*n := (countedAppend_work comp.1 tail.1).le.trans (by omega)
    change ma.2+first.2+coins.2+md.2+q.2+f.2+tail.2+comp.2+out.2+10≤_
    change _≤(1+2*n)+(1+n*C)+(1+n*(C+3))+(1+2*n)+(1+n*C)+C+(1+n*(C+3))+(1+3*n)+(1+2*n)+10
    omega

end ProphetSecretary.Statistics
