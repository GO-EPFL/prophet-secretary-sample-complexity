import ProphetSecretary.Statistics.CanonicalBitArrayWork
import ProphetSecretary.Statistics.PlannerArithmeticOperands

/-!
# Hard bit work of the multilevel loop

The height bound for the returned recursive value is separate from the
heights of the unnormalized averages and paired differences at its parent.
The latter are bounded before charging their binary operations.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

private lemma canonicalAverage_height (d : ℕ) (f : Fin (4^d) → BinaryRational × ℕ) (B : ℕ)
    (h : ∀ i, RationalHeight (f i).1.value B) :
    RationalHeight (countedCanonicalAverage d f).1.value (4^d*(B+1)+2*d) := by
  rw [countedCanonicalAverage_value]
  change RationalHeight (BinaryRational.valueHom ((1/(4:BinaryRational)^d)*∑ i,(f i).1)) _
  rw [map_mul,map_div₀,map_one,map_pow,map_ofNat,map_sum]
  have hS := rationalHeight_sum Finset.univ (fun i => (f i).1.value) (fun _ => B) (fun i _ => h i)
  have hS' : RationalHeight (∑ i,(f i).1.value) (4^d*(B+1)) := by simpa [nsmul_eq_mul] using hS
  exact ((rationalHeight_averageCoefficient d).mul hS').mono (by omega)

def canonicalTreeBitUnit (R B P : ℕ) : ℕ :=
  let F := 4^R
  let A := 2*B+2*R+5
  let Q := F*(A+1)+2*R
  let U := B+Q+R*(Q+1)+3
  let M := binaryArrayCharge (2*(F+R)+11) U
  let C := 3600*(U+2)^3
  P+F*(2*P+2)+8*F+4+M+(8*R+4+M)+R*(F*(4*P+C+6)+8*F+4+M)+M+8

namespace CountedPlannerRecursion

variable {State Context Seed Transition : Type*}

set_option maxHeartbeats 400000 in
theorem canonicalEstimate_work (D : CountedPlannerRecursion State Context Seed Transition BinaryRational)
    (G : ℕ → State → Prop) (R B V P : ℕ)
    (hPrepare : ∀ r x, r≤R → G r x →
      let q := D.prepare x
      q.2≤P ∧ RationalHeight q.1.offset.value B ∧ RationalHeight q.1.coefficient.value B)
    (hSample : ∀ r x s, r≤R → G r x → (D.sample (D.prepare x).1.context s).2≤P)
    (hChild : ∀ r x s j, r≤R → G r x → j<r →
      let q := (D.prepare x).1.context
      let child := D.child q (D.sample q s).1
      child.2≤P ∧ G j child.1)
    (hPayoff : ∀ r x s a, r≤R → G r x → RationalHeight a.value V →
      let q := (D.prepare x).1.context
      let pay := D.payoff q (D.sample q s).1 a
      pay.2≤P ∧ RationalHeight pay.1.value B)
    (hValue : ∀ r x t, r≤R → G r x → RationalHeight (D.estimate r x t).1.value V)
    (r : ℕ) (hr : r≤R) (x : State) (hx : G r x) (t : MultilevelTree Seed r) :
    (D.canonicalEstimate r x t).2≤canonicalTreeBitUnit R B P*multilevelTreeWork r t := by
  let F := 4^R
  let A := 2*B+2*R+5
  let Q := F*(A+1)+2*R
  let U := B+Q+R*(Q+1)+3
  let M := binaryArrayCharge (2*(F+R)+11) U
  let C := 3600*(U+2)^3
  let W := canonicalTreeBitUnit R B P
  let J := F*(4*P+C+6)+8*F+4+M
  have hW : W=P+F*(2*P+2)+8*F+4+M+(8*R+4+M)+R*J+M+8 := rfl
  have hB : B≤A := by dsimp [A]; omega
  have hA : A≤U := by
    have h := Nat.le_mul_of_pos_left (A+1) (show 0<F by dsimp [F]; positivity)
    dsimp only [Q,U]
    omega
  have hQU : Q≤U := by dsimp [U]; omega
  have hBU : B≤U := by dsimp [U]; omega
  have h3U : 3≤U := by dsimp [U]; omega
  have hAvg (d : ℕ) (f : Fin (4^d) → BinaryRational × ℕ) (hd : d≤R)
      (hf : ∀ i, RationalHeight (f i).1.value A) :
      (countedCanonicalAverage d f).2≤(∑ i,(f i).2)+8*F+4+M ∧
        RationalHeight (countedCanonicalAverage d f).1.value Q := by
    have hF : 4^d≤F := Nat.pow_le_pow_right (by decide) hd
    have hCharge := binaryArrayCharge_mono (W := 2*4^d+5) (W' := 2*(F+R)+11) (by omega) hA
    have h₁ := countedCanonicalAverage_work d f A (by dsimp [A]; omega) hf
    have h₂ := canonicalAverage_height d f A hf
    refine ⟨h₁.trans (by change _≤(∑ i,(f i).2)+8*F+4+binaryArrayCharge (2*(F+R)+11) U; omega),h₂.mono ?_⟩
    have h' := Nat.mul_le_mul_right (A+1) hF
    dsimp [Q]
    omega
  change (D.canonicalEstimate r x t).2≤W*multilevelTreeWork r t
  induction r using Nat.strong_induction_on generalizing x with
  | h r ih =>
    cases t with
    | zero =>
      simp only [canonicalEstimate,multilevelTreeWork,Nat.mul_one]
      rw [hW]
      omega
    | @node d base tr up lo =>
      let q := D.prepare x
      have hq := hPrepare (d+1) x hr hx
      by_cases he : q.1.empty=true
      · simp only [canonicalEstimate,multilevelTreeWork,show (D.prepare x).1.empty=true from he,if_true]
        change q.2+2≤_
        have hq' : q.2≤P := hq.1
        have h₁ : q.2+2≤W := by rw [hW]; omega
        have hPos : 0 < 1+4^(d+1)+∑ l : Fin d,∑ j : Fin (4^(d-l.val)),
            (1+multilevelTreeWork (l.val+1) (up l j)+multilevelTreeWork l.val (lo l j)) :=
          Nat.add_pos_left (Nat.add_pos_left (by decide) _) _
        exact h₁.trans (Nat.le_mul_of_pos_right W hPos)
      · let f := fun j : Fin (4^(d+1)) =>
          let y := D.sample q.1.context (base j)
          let a := D.payoff q.1.context y.1 0
          (a.1,y.2+a.2+2)
        let g := fun (l : Fin d) (j : Fin (4^(d-l.val))) =>
          let y := D.sample q.1.context (tr l j)
          let u := D.child q.1.context y.1
          let a := D.canonicalEstimate (l.val+1) u.1 (up l j)
          let b := D.canonicalEstimate l.val u.1 (lo l j)
          let ap := D.payoff q.1.context y.1 a.1
          let bp := D.payoff q.1.context y.1 b.1
          let s := BinaryRational.countedOperation .sub ap.1 bp.1
          (s.1,y.2+u.2+a.2+b.2+ap.2+bp.2+s.2+6)
        let U₀ := fun (l : Fin d) j => multilevelTreeWork (l.val+1) (up l j)
        let L₀ := fun (l : Fin d) j => multilevelTreeWork l.val (lo l j)
        let S := ∑ l : Fin d, ∑ j : Fin (4^(d-l.val)), (U₀ l j+L₀ l j)
        have h0 : RationalHeight (0:BinaryRational).value V := by
          rw [BinaryRational.zero_value]
          exact rationalHeight_zero.mono (Nat.zero_le _)
        have hf (j : Fin (4^(d+1))) : (f j).2≤2*P+2 ∧ RationalHeight (f j).1.value A := by
          have h := hPayoff (d+1) x (base j) 0 hr hx h0
          have hs := hSample (d+1) x (base j) hr hx
          exact ⟨by dsimp [f,q]; omega,h.2.mono hB⟩
        have hg (l : Fin d) (j : Fin (4^(d-l.val))) :
            (g l j).2≤W*(U₀ l j+L₀ l j)+(4*P+C+6) ∧ RationalHeight (g l j).1.value A := by
          let y := D.sample q.1.context (tr l j)
          let u := D.child q.1.context y.1
          let a := D.canonicalEstimate (l.val+1) u.1 (up l j)
          let b := D.canonicalEstimate l.val u.1 (lo l j)
          let ap := D.payoff q.1.context y.1 a.1
          let bp := D.payoff q.1.context y.1 b.1
          let s := BinaryRational.countedOperation .sub ap.1 bp.1
          have hu : l.val+1<d+1 := by have := l.isLt; omega
          have hl : l.val<d+1 := by have := l.isLt; omega
          have hChildU := hChild (d+1) x (tr l j) (l.val+1) hr hx hu
          have hChildL := hChild (d+1) x (tr l j) l.val hr hx hl
          have hy : y.2≤P := hSample _ x (tr l j) hr hx
          have hc : u.2≤P := hChildU.1
          have hAW : a.2≤W*U₀ l j := ih _ hu (hu.le.trans hr) u.1 hChildU.2 (up l j)
          have hBW : b.2≤W*L₀ l j := ih _ hl (hl.le.trans hr) u.1 hChildL.2 (lo l j)
          have ha : RationalHeight a.1.value V := by
            rw [CountedPlannerRecursion.canonicalEstimate_value]
            exact hValue _ u.1 _ (hu.le.trans hr) hChildU.2
          have hb : RationalHeight b.1.value V := by
            rw [CountedPlannerRecursion.canonicalEstimate_value]
            exact hValue _ u.1 _ (hl.le.trans hr) hChildL.2
          have hAp := hPayoff _ x (tr l j) a.1 hr hx ha
          have hBp := hPayoff _ x (tr l j) b.1 hr hx hb
          have hAp' : ap.2≤P ∧ RationalHeight ap.1.value B := hAp
          have hBp' : bp.2≤P ∧ RationalHeight bp.1.value B := hBp
          have hs : s.2≤C := BinaryRational.countedOperation_work .sub ap.1 bp.1 U
            (hAp'.2.mono hBU) (hBp'.2.mono hBU)
          constructor
          · change y.2+u.2+a.2+b.2+ap.2+bp.2+s.2+6≤_
            rw [Nat.mul_add]
            omega
          · change RationalHeight s.1.value A
            have heq : s.1.value=ap.1.value-bp.1.value := by
              rw [show s=(BinaryRational.countedOperation .sub ap.1 bp.1) from rfl,BinaryRational.countedOperation_value]
              exact BinaryRational.sub_value _ _
            rw [heq]
            exact (hAp'.2.sub hBp'.2).mono (by dsimp [A]; omega)
        let baseAvg := countedCanonicalAverage (d+1) f
        let av := fun l : Fin d => countedCanonicalAverage (d-l.val) (g l)
        let pair := countedCanonicalArraySum av
        have hBase := hAvg (d+1) f hr (fun j => (hf j).2)
        have hAV (l : Fin d) := hAvg (d-l.val) (g l) ((Nat.sub_le _ _).trans (Nat.le_of_succ_le hr)) (fun j => (hg l j).2)
        have hBaseW : baseAvg.2≤F*(2*P+2)+8*F+4+M := by
          refine hBase.1.trans ?_
          have h : (∑ j,(f j).2)≤∑ _j : Fin (4^(d+1)), (2*P+2) := Finset.sum_le_sum (fun j _ => (hf j).1)
          have hF : 4^(d+1)≤F := Nat.pow_le_pow_right (by decide) hr
          have h' : (∑ j,(f j).2)≤F*(2*P+2) :=
            h.trans (by simpa using Nat.mul_le_mul_right (2*P+2) hF)
          omega
        have hAVW (l : Fin d) : (av l).2≤W*(∑ j : Fin (4^(d-l.val)), (U₀ l j+L₀ l j))+J := by
          refine (hAV l).1.trans ?_
          have h : (∑ j,(g l j).2)≤(∑ j : Fin (4^(d-l.val)), (W*(U₀ l j+L₀ l j)+(4*P+C+6))) :=
            Finset.sum_le_sum (s := Finset.univ) (fun j _ => (hg l j).1)
          have hF : 4^(d-l.val)≤F := Nat.pow_le_pow_right (by decide) ((Nat.sub_le _ _).trans (Nat.le_of_succ_le hr))
          have heq : (∑ j : Fin (4^(d-l.val)), (W*(U₀ l j+L₀ l j)+(4*P+C+6))) =
              W*(∑ j : Fin (4^(d-l.val)), (U₀ l j+L₀ l j))+4^(d-l.val)*(4*P+C+6) := by
            rw [Finset.sum_add_distrib,← Finset.mul_sum]
            simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
          rw [heq] at h
          have h' := Nat.mul_le_mul_right (4*P+C+6) hF
          unfold J
          omega
        have hPairW := countedCanonicalArraySum_work av Q (fun l => (hAV l).2)
        have hd : d≤R := Nat.le_of_succ_le hr
        have hM := binaryArrayCharge_mono (W := 2*d+1) (W' := 2*(F+R)+11) (by omega) hQU
        have hSum : (∑ l,(av l).2)≤(∑ l : Fin d, (W*(∑ j : Fin (4^(d-l.val)),(U₀ l j+L₀ l j))+J)) :=
          Finset.sum_le_sum (s := Finset.univ) (fun l _ => hAVW l)
        have heq : (∑ l : Fin d, (W*(∑ j : Fin (4^(d-l.val)),(U₀ l j+L₀ l j))+J)) = W*S+d*J := by
          rw [Finset.sum_add_distrib,← Finset.mul_sum]
          simp only [S,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
        rw [heq] at hSum
        have hdJ := Nat.mul_le_mul_right J hd
        have hPair : pair.2≤W*S+R*J+8*R+4+M := by
          change (countedCanonicalArraySum av).2≤_
          change (∑ l,(av l).2)≤W*S+d*J at hSum
          change binaryArrayCharge (2*d+1) Q≤M at hM
          omega
        have hPH : RationalHeight pair.1.value (R*(Q+1)) := by
          rw [countedCanonicalArraySum_value]
          change RationalHeight (BinaryRational.valueHom (∑ l,(av l).1)) _
          rw [map_sum]
          have h := rationalHeight_sum Finset.univ (fun l => (av l).1.value) (fun _ => Q) (fun l _ => (hAV l).2)
          exact h.mono (by simpa using Nat.mul_le_mul_right (Q+1) hd)
        let v := countedCanonicalUpdate q.1.offset q.1.coefficient baseAvg.1 pair.1
        have hv := countedCanonicalUpdate_work q.1.offset q.1.coefficient baseAvg.1 pair.1 U h3U
          (hq.2.1.mono hBU) (hq.2.2.mono hBU) (hBase.2.mono hQU) (hPH.mono (by dsimp [U]; omega))
        have hMV := binaryArrayCharge_mono (B := U) (B' := U) (W := 11) (W' := 2*(F+R)+11) (by omega) le_rfl
        have hvW : v.2≤M+3 := hv.trans (Nat.add_le_add_right hMV 3)
        rw [canonicalEstimate,if_neg he]
        change q.2+baseAvg.2+pair.2+v.2+4≤_
        have hLocal : q.2+baseAvg.2+pair.2+v.2+4≤W*(1+S) := by
          rw [Nat.mul_add,Nat.mul_one]
          have hqW : q.2≤P := hq.1
          omega
        refine hLocal.trans (Nat.mul_le_mul_left _ ?_)
        simp only [multilevelTreeWork]
        have hST : S≤∑ l : Fin d,∑ j : Fin (4^(d-l.val)),(1+U₀ l j+L₀ l j) := by
          exact Finset.sum_le_sum (fun l _ => Finset.sum_le_sum (fun j _ => by omega))
        change 1+S≤1+4^(d+1)+(∑ l : Fin d,∑ j : Fin (4^(d-l.val)),(1+U₀ l j+L₀ l j))
        exact (Nat.add_le_add_left hST 1).trans (Nat.add_le_add_right (Nat.le_add_right 1 _) _)

end CountedPlannerRecursion

end ProphetSecretary.Statistics
