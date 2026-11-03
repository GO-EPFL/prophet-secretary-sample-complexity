import ProphetSecretary.Statistics.CalibratedOuter.FairMarkExecution
import ProphetSecretary.Statistics.PlannerRationalDecode
import ProphetSecretary.Analysis.MultilevelSeedTape

/-!
# Allocating the reserved outer marks

One mark is allocated for every possible training or online coordinate.
Allocating the complete array makes both the hard count and the mark-only
collision event independent of the branch eventually used.
-/

open MeasureTheory
open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m : ℕ}

def sampleOuterMarksM {M : Type → Type} [Monad M] {K : Type}
    (n m : ℕ) (uniform : M K) : M (OuterMarkArray n m K × ℕ) := do
  let q ← Vector.ofFnM (fun _ : Fin (outerMarkSlotCount n m) => uniform)
  pure (q.get,4*(outerMarkSlotCount n m+1))

def sampleOuterMarkBitsM {M : Type → Type} [Monad M] (n m b : ℕ) (bit : M Bool) :
    M (OuterMarkArray n m (Fin b → Bool) × ℕ) := do
  let q ← Vector.ofFnM (fun _ : Fin (outerMarkSlotCount n m) =>
    Vector.ofFnM (fun _ : Fin b => bit))
  pure (fun i j => (q.get i).get j,8*(outerMarkSlotCount n m+1)*(b+1))

private lemma outerMarkCounter_bind {A B : Type} (x : StateM ℕ A)
    (f : A → StateM ℕ B) (c : ℕ) :
    ((x >>= f).run c).2=((f (x.run c).1).run (x.run c).2).2 := rfl

private lemma outerMarkCounter_pure {A : Type} (x : A) (c : ℕ) :
    ((pure x : StateM ℕ A).run c).2=c := rfl

lemma sampleOuterMarksM_counter {K : Type} (n m : ℕ) (uniform : StateM ℕ K)
    (h : ∀ c, (uniform.run c).2=c+1) (c : ℕ) :
    ((sampleOuterMarksM n m uniform).run c).2=c+outerMarkSlotCount n m := by
  simp only [sampleOuterMarksM,outerMarkCounter_bind,outerMarkCounter_pure,
    uniformVectorM_counter uniform 1 h,Nat.mul_one]

lemma sampleOuterMarkBitsM_counter (n m b : ℕ) (bit : StateM ℕ Bool)
    (h : ∀ c, (bit.run c).2=c+1) (c : ℕ) :
    ((sampleOuterMarkBitsM n m b bit).run c).2=c+outerMarkSlotCount n m*b := by
  have hb (x : ℕ) : ((Vector.ofFnM (fun _ : Fin b => bit)).run x).2=x+b := by
    simpa only [Nat.mul_one] using uniformVectorM_counter bit 1 h b x
  simp only [sampleOuterMarkBitsM,outerMarkCounter_bind,outerMarkCounter_pure,
    uniformVectorM_counter _ b hb]

lemma sampleOuterMarksM_work {K : Type} (n m : ℕ) (uniform : StateM ℕ K) (c : ℕ) :
    ((sampleOuterMarksM n m uniform).run c).1.2=4*(outerMarkSlotCount n m+1) := rfl

lemma sampleOuterMarkBitsM_work (n m b : ℕ) (bit : StateM ℕ Bool) (c : ℕ) :
    ((sampleOuterMarkBitsM n m b bit).run c).1.2=8*(outerMarkSlotCount n m+1)*(b+1) := rfl

def countedOuterMarkDecode (b : ℕ) (bits : OuterMarkArray n m (Fin b → Bool)) :
    OuterMarkArray n m ℚ × ℕ :=
  let q := Vector.ofFn (fun i => countedStoredDyadicUniform b (bits i))
  (fun i => (q.get i).1,(∑ i : Fin (outerMarkSlotCount n m), ((q.get i).2+3))+2)

private lemma vector_get_ofFn {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i=f i := Vector.getElem_ofFn i.isLt

lemma countedOuterMarkDecode_value (b : ℕ) (bits : OuterMarkArray n m (Fin b → Bool)) (j) :
    ((countedOuterMarkDecode b bits).1 j : ℝ)=fairMarkDecoder b bits j := by
  simp only [countedOuterMarkDecode,vector_get_ofFn,countedStoredDyadicUniform_value,
    countedDyadicUniform,countedFairBitsIndex_value,fairMarkDecoder,gridPoint_ratCast]

lemma countedOuterMarkDecode_work (b : ℕ) (bits : OuterMarkArray n m (Fin b → Bool)) :
    (countedOuterMarkDecode b bits).2≤outerMarkSlotCount n m*(12*b+10)+2 := by
  simp only [countedOuterMarkDecode,vector_get_ofFn]
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _i : Fin (outerMarkSlotCount n m), (12*b+10) := by
      apply Finset.sum_le_sum
      intro i _
      have h := countedStoredDyadicUniform_work b (bits i)
      omega
    _ = _ := by simp

end ProphetSecretary.Statistics.Calibration
