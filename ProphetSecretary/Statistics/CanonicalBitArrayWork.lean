import ProphetSecretary.Statistics.CanonicalBitTree

/-!
# Binary work of the tree's numerical blocks

Each block's extra cost is the counted expression evaluation, in addition
to the already measured cost of producing its array entries.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ArithmeticExpression

def binaryArrayCharge (W B : ℕ) : ℕ := W*(3600*((B+1)*W+2)^3)

lemma binaryArrayCharge_mono {W W' B B' : ℕ} (hW : W≤W') (hB : B≤B') :
    binaryArrayCharge W B≤binaryArrayCharge W' B' := by
  have h := Nat.add_le_add_right (Nat.mul_le_mul (Nat.add_le_add_right hB 1) hW) 2
  exact Nat.mul_le_mul hW (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h 3))

private lemma canonicalWorkVectorGet {α : Type*} {K : ℕ} (f : Fin K → α) (i : Fin K) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

theorem countedCanonicalArraySum_work {K : ℕ} (f : Fin K → BinaryRational × ℕ) (B : ℕ)
    (h : ∀ i, RationalHeight (f i).1.value B) :
    (countedCanonicalArraySum f).2≤(∑ i,(f i).2)+8*K+4+binaryArrayCharge (2*K+1) B := by
  let e := sumList (List.finRange K) ArithmeticExpression.input
  have he : LiteralsBounded B e := literalsBounded_sumList _ _ _ (fun _ _ => trivial)
  have hw : e.work≤2*K+1 := by
    have h' := work_sumList_le (List.finRange K) ArithmeticExpression.input 1 (fun _ _ => le_rfl)
    simpa only [e,List.length_finRange,Nat.mul_comm,Nat.add_comm] using h'
  have hW := countedCanonicalEval_work_le (fun i => (f i).1) B (2*K+1) h e he hw
  simp only [countedCanonicalArraySum,canonicalWorkVectorGet]
  change (countedCanonicalEval (fun i => (f i).1) e).2+_+8*K+4≤_
  unfold binaryArrayCharge
  omega

theorem countedCanonicalAverage_work (d : ℕ) (f : Fin (4^d) → BinaryRational × ℕ) (B : ℕ)
    (hB : 2*d≤B) (h : ∀ i, RationalHeight (f i).1.value B) :
    (countedCanonicalAverage d f).2≤(∑ i,(f i).2)+8*4^d+4+binaryArrayCharge (2*4^d+5) B := by
  let e := multilevelAverageExpression d
  have hPow : ((4:ℤ)^d).natAbs≤2^B := by
    rw [Int.natAbs_pow,show (4:ℤ).natAbs=2^2 by decide,← pow_mul]
    exact Nat.pow_le_pow_right (by decide) hB
  have he : LiteralsBounded B e :=
    ⟨⟨Nat.succ_le_of_lt (by positivity),hPow⟩,literalsBounded_sumList _ _ _ (fun _ _ => trivial)⟩
  have hW := countedCanonicalEval_work_le (fun i => (f i).1) B (2*4^d+5) h e he (multilevelAverageExpression_work d)
  simp only [countedCanonicalAverage,canonicalWorkVectorGet]
  change (countedCanonicalEval (fun i => (f i).1) e).2+_+8*4^d+4≤_
  unfold binaryArrayCharge
  omega

theorem countedCanonicalUpdate_work (o c b p : BinaryRational) (B : ℕ) (hB : 3≤B)
    (ho : RationalHeight o.value B) (hc : RationalHeight c.value B)
    (hb : RationalHeight b.value B) (hp : RationalHeight p.value B) :
    (countedCanonicalUpdate o c b p).2≤binaryArrayCharge 11 B+3 := by
  let x : Fin 4 → BinaryRational := ![o,c,b,p]
  have hx (i : Fin 4) : RationalHeight (x i).value B := by fin_cases i <;> assumption
  have hL₀ : LiteralsBounded 3 multilevelUpdateExpression := by norm_num [multilevelUpdateExpression,LiteralsBounded]
  have h := countedCanonicalEval_work_le x B 11 hx _ (hL₀.mono hB) (by decide)
  exact Nat.add_le_add_right h 3

end ProphetSecretary.Statistics
