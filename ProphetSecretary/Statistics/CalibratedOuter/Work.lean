import ProphetSecretary.Statistics.CalibratedOuter.PreparedExecution
import ProphetSecretary.Analysis.MultilevelSeedTape

/-!
# Counted execution of the outer display rule

The outer preparation is stored once. Each online step applies the display
map only to the current and past observations and calls the inner decision
with the transformed history. The original value remains the reward.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model

variable {n m : ℕ} {K T : Type*} [Field K] [LinearOrder K]

def countedOuterHistory (m : ℕ) (H : K) (cutoff : K × K) (tags : Fin n → K)
    (hist : Fin n → Option (T × K)) : (Fin n → Option (T × K)) × ℕ :=
  let v : Vector (Option (T × K) × ℕ) n := Vector.ofFn fun i =>
    match hist i with
    | none => (none,2)
    | some (t,x) =>
      let a := countedDisplay m H cutoff (x,tags i)
      (some (t,a.1),a.2+6)
  (fun i => (v.get i).1,(∑ i : Fin n,(v.get i).2)+3)

private lemma vector_get_ofFn {α : Type*} {k : ℕ} (f : Fin k → α) (i : Fin k) :
    (Vector.ofFn f).get i = f i := Vector.getElem_ofFn i.isLt

lemma countedOuterHistory_work (m : ℕ) (H : K) (cutoff : K × K) (tags : Fin n → K)
    (hist : Fin n → Option (T × K)) :
    (countedOuterHistory m H cutoff tags hist).2≤n*(4*m+24)+3 := by
  unfold countedOuterHistory
  dsimp only
  simp only [vector_get_ofFn]
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _i : Fin n, (4*m+24) := by
      apply Finset.sum_le_sum
      intro i _
      cases e : hist i with
      | none => simp only; omega
      | some z =>
        obtain ⟨t,x⟩ := z
        change (countedDisplay m H cutoff (x,tags i)).2+6≤4*m+24
        have h := countedDisplay_work m H cutoff (x,tags i)
        omega
    _ = _ := by simp

def countedOuterOnline (q : CountedOuterPreparation K n m) (tags : Fin n → K)
    (inner : T → Fin n → K → (Fin n → Option (T × K)) → Bool × ℕ)
    (t : T) (i : Fin n) (x : K) (hist : Fin n → Option (T × K)) : Bool × ℕ :=
  if q.pilot=0 then (decide (0<countedRetention q.cutoff (x,tags i)),7)
  else
    let H := 1000*q.pilot
    let a := countedDisplay m H q.cutoff (x,tags i)
    let h := countedOuterHistory m H q.cutoff tags hist
    let out := inner t i a.1 h.1
    (out.1,out.2+a.2+h.2+6)

theorem countedOuterOnline_work (q : CountedOuterPreparation K n m) (tags : Fin n → K)
    (inner : T → Fin n → K → (Fin n → Option (T × K)) → Bool × ℕ)
    (t : T) (i : Fin n) (x : K) (hist : Fin n → Option (T × K)) (W : ℕ)
    (hW : ∀ x h, (inner t i x h).2≤W) :
    (countedOuterOnline q tags inner t i x hist).2≤W+(n+1)*(4*m+24)+9 := by
  unfold countedOuterOnline
  split_ifs
  · change 7≤_
    omega
  · dsimp only
    have hD := countedDisplay_work m (1000*q.pilot) q.cutoff (x,tags i)
    have hH := countedOuterHistory_work m (1000*q.pilot) q.cutoff tags hist
    have h := hW (countedDisplay m (1000*q.pilot) q.cutoff (x,tags i)).1
      (countedOuterHistory m (1000*q.pilot) q.cutoff tags hist).1
    rw [Nat.add_mul]
    omega

lemma countedOuterHistory_value (m : ℕ) (H : ℝ) (cutoff : ℝ × ℝ) (tags : Fin n → ℝ)
    (hist : History n) :
    (countedOuterHistory m H cutoff tags hist).1 =
      mapHistoryValuesBy (fun j y => outerMeshDisplay m H (retainAboveTag cutoff (y,tags j))) hist := by
  funext j
  simp only [countedOuterHistory,vector_get_ofFn,mapHistoryValuesBy]
  cases e : hist j with
  | none => rfl
  | some z =>
    obtain ⟨s,y⟩ := z
    simp [mapObservationValues,countedDisplay_value]

/-- Instantiating the inner decision with its stored learner state recovers
the prepared arithmetic outer rule at every raw observation history. -/
lemma countedOuterOnline_value (q : CountedOuterPreparation ℝ n m) (L : Learner n (2*m))
    (r : L.Seed) (tags : Fin n → ℝ) (cost : ℝ → Fin n → ℝ → History n → ℕ)
    (t : ℝ) (i : Fin n) (x : ℝ) (hist : History n) :
    (countedOuterOnline q tags (fun s j y H => (L.policy.decide (q.displayed,r) s j y H,cost s j y H))
      t i x hist).1 = decidePreparedOuter m L q r tags t i x hist := by
  unfold countedOuterOnline decidePreparedOuter
  split_ifs
  · rfl
  · dsimp only
    rw [countedOuterHistory_value]
    simp only [countedDisplay_value]

section Training
open ProphetSecretary.Analysis

/-- Read each prescribed row in order. The unknown laws are accessed only
through the identity-indexed sampling primitive. -/
def countedFullSamplesM {M : Type → Type} [Monad M] {A : Type}
    (n k : ℕ) (sample : Fin n → M A) : M ((Fin n → Fin k → A) × ℕ) := do
  let q ← Vector.ofFnM (fun i : Fin n => Vector.ofFnM (fun _ : Fin k => sample i))
  pure (fun i j => (q.get i).get j,8*(n+1)*(k+1))

private lemma fullSampleCounter_bind {A B : Type} (x : StateM ℕ A)
    (f : A → StateM ℕ B) (c : ℕ) :
    ((x >>= f).run c).2=((f (x.run c).1).run (x.run c).2).2 := rfl

private lemma fullSampleCounter_pure {A : Type} (x : A) (c : ℕ) :
    ((pure x : StateM ℕ A).run c).2=c := rfl

private lemma fullSampleVector_counter {A : Type} {n : ℕ}
    (f : Fin n → StateM ℕ A) (D : ℕ)
    (h : ∀ i c, ((f i).run c).2=c+D) (c : ℕ) :
    ((Vector.ofFnM f).run c).2=c+n*D := by
  induction n with
  | zero => rw [Vector.ofFnM_zero,fullSampleCounter_pure]; omega
  | succ n ih =>
    rw [Vector.ofFnM_succ,fullSampleCounter_bind,fullSampleCounter_bind,fullSampleCounter_pure,h]
    rw [ih _ (fun i c => h _ c)]
    simp [Nat.succ_mul,Nat.add_assoc]

lemma countedFullSamplesM_counter {A : Type} (n k : ℕ) (sample : Fin n → StateM ℕ A)
    (h : ∀ i c, ((sample i).run c).2=c+1) (c : ℕ) :
    ((countedFullSamplesM n k sample).run c).2=c+n*k := by
  unfold countedFullSamplesM
  rw [fullSampleCounter_bind,fullSampleCounter_pure]
  apply fullSampleVector_counter
  intro i a
  simpa only [Nat.mul_one] using uniformVectorM_counter (sample i) 1 (h i) k a

lemma countedFullSamplesM_work {A : Type} (n k : ℕ) (sample : Fin n → StateM ℕ A) (c : ℕ) :
    ((countedFullSamplesM n k sample).run c).1.2=8*(n+1)*(k+1) := rfl

end Training

end ProphetSecretary.Statistics.Calibration
