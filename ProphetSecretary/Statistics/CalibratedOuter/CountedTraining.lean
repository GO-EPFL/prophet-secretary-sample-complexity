import ProphetSecretary.Statistics.CalibratedOuter.Learner
import ProphetSecretary.Probability.CountedOrderStatistic
import ProphetSecretary.Statistics.CalibratedOuter.CountedMesh

/-!
# Counted outer training statistics

The cutoff uses linear scans of the tagged rows. The pilot takes one order
statistic of the retained maxima. Both operate only on observed samples and
their independent tags.
-/

open scoped Classical BigOperators NNReal

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Probability

variable {n m : ℕ}

def countedMaximumFrom {α : Type*} [LinearOrder α] : α → List α → α × ℕ
  | a, [] => (a,1)
  | a, b :: l => let q := countedMaximumFrom (max a b) l; (q.1,q.2+2)

lemma countedMaximumFrom_le_iff {α : Type*} [LinearOrder α] (a c : α) (l : List α) :
    (countedMaximumFrom a l).1 ≤ c ↔ a ≤ c ∧ ∀ b ∈ l, b ≤ c := by
  induction l generalizing a with
  | nil => simp [countedMaximumFrom]
  | cons b l ih =>
    simp only [countedMaximumFrom, ih, max_le_iff, List.mem_cons]
    constructor
    · rintro ⟨⟨ha,hb⟩,hl⟩
      exact ⟨ha,fun d h => h.elim (fun e => e.symm ▸ hb) (hl d)⟩
    · rintro ⟨ha,hl⟩
      exact ⟨⟨ha,hl b (Or.inl rfl)⟩,fun d h => hl d (Or.inr h)⟩

lemma countedMaximumFrom_work {α : Type*} [LinearOrder α] (a : α) (l : List α) :
    (countedMaximumFrom a l).2 = 2*l.length+1 := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp only [countedMaximumFrom, ih, List.length_cons]; omega

def countedFiniteMaximum {α : Type*} [LinearOrder α] (hn : 0<n) (f : Fin n → α) : α × ℕ :=
  let q := countedMaximumFrom (f ⟨0,hn⟩) (List.ofFn f)
  (q.1,q.2+n+1)

def countedFiniteMinimum {α : Type*} [LinearOrder α] (hn : 0<n) (f : Fin n → α) : α × ℕ :=
  countedFiniteMaximum (α := αᵒᵈ) hn f

lemma countedFiniteMaximum_value {α : Type*} [LinearOrder α] (hn : 0<n) (f : Fin n → α) :
    (countedFiniteMaximum hn f).1 = Finset.univ.sup' (outerOfferIndices_nonempty hn) f := by
  apply eq_of_forall_ge_iff
  intro c
  change (countedMaximumFrom (f ⟨0,hn⟩) (List.ofFn f)).1 ≤ c ↔ _
  rw [countedMaximumFrom_le_iff, Finset.sup'_le_iff]
  constructor
  · intro h i _
    exact h.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro h
    refine ⟨h _ (Finset.mem_univ _), ?_⟩
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact h i (Finset.mem_univ _)

lemma countedFiniteMinimum_value {α : Type*} [LinearOrder α] (hn : 0<n) (f : Fin n → α) :
    (countedFiniteMinimum hn f).1 = Finset.univ.inf' (outerOfferIndices_nonempty hn) f :=
  countedFiniteMaximum_value (α := αᵒᵈ) hn f

lemma countedFiniteMaximum_work {α : Type*} [LinearOrder α] (hn : 0<n) (f : Fin n → α) :
    (countedFiniteMaximum hn f).2 = 3*n+2 := by
  simp only [countedFiniteMaximum, countedMaximumFrom_work, List.length_ofFn]
  omega

def countedCutoff {K : Type*} [LinearOrder K] [Zero K] (hm : 1≤m)
    (a : Fin m → Fin n → K × K) : (K × K) × ℕ :=
  if hn : 0<n then
    let rows := fun r => countedFiniteMaximum (α := Lex (K × K)) hn (fun i => toLex (a r i))
    let q := countedFiniteMinimum (show 0<m by omega) (fun r => (rows r).1)
    (ofLex q.1, q.2 + ∑ r, (rows r).2 + 2)
  else ((0,0),1)

lemma countedCutoff_value (hm : 1≤m) (a : Fin m → Fin n → ℝ × ℝ) :
    (countedCutoff hm a).1 = ofLex (outerCutoffTaggedRows m hm a) := by
  unfold countedCutoff outerCutoffTaggedRows
  split_ifs
  · simp only [countedFiniteMinimum_value, countedFiniteMaximum_value, outerTaggedMaximum]
  · rfl

lemma countedCutoff_work {K : Type*} [LinearOrder K] [Zero K] (hm : 1≤m)
    (a : Fin m → Fin n → K × K) :
    (countedCutoff hm a).2 ≤ 10*(m+1)*(n+1) := by
  unfold countedCutoff
  split_ifs
  · dsimp only
    simp only [countedFiniteMinimum, countedFiniteMaximum_work, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    nlinarith
  · change 1 ≤ 10*(m+1)*(n+1)
    exact Nat.succ_le_of_lt (by positivity)

def countedRetainedMaximum {K : Type*} [LinearOrder K] [Zero K] (t : K × K)
    (a : Fin n → K × K) : K × ℕ :=
  let q := countedMaximumFrom 0 (List.ofFn fun i =>
    if (toLex t : Lex (K × K)) < toLex (a i) then (a i).1 else 0)
  (q.1,q.2+4*n+1)

lemma countedRetainedMaximum_value (t : ℝ × ℝ) (a : Fin n → ℝ × ℝ) :
    (countedRetainedMaximum t a).1 = retainedMaximumAtTag t a := by
  let f := retainedTaggedVector t a
  have hf (i : Fin n) : (if (toLex t : TaggedValue) < toLex (a i) then (a i).1 else 0) = f i := by
    unfold f retainedTaggedVector retainAboveTag
    by_cases h : taggedAbove t (a i) <;> simp only [← taggedAbove_iff_lex_lt, h, if_true, if_false]
  apply eq_of_forall_ge_iff
  intro c
  unfold countedRetainedMaximum retainedMaximumAtTag Instance.maximum
  dsimp only
  simp_rw [hf]
  rw [countedMaximumFrom_le_iff, Finset.sup'_le_iff]
  constructor
  · intro h i _
    cases i with
    | none => exact h.1
    | some i => exact h.2 _ (List.mem_ofFn.mpr ⟨i,rfl⟩)
  · intro h
    refine ⟨h none (Finset.mem_univ _), ?_⟩
    intro x hx
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
    exact h (some i) (Finset.mem_univ _)

lemma countedRetainedMaximum_work {K : Type*} [LinearOrder K] [Zero K] (t : K × K)
    (a : Fin n → K × K) :
    (countedRetainedMaximum t a).2 = 6*n+2 := by
  simp only [countedRetainedMaximum, countedMaximumFrom_work, List.length_ofFn]
  omega

def countedPilot {K : Type*} [LinearOrder K] [Zero K] (hm : 1≤m) (t : K × K)
    (a : Fin (outerPilotRounds m) → Fin n → K × K) : K × ℕ :=
  let r := outerPilotRank m
  let k : Fin (outerPilotRounds m) := ⟨r-1, by
    have hr := outerPilotRank_pos hm
    unfold outerPilotRounds
    dsimp [r]
    omega⟩
  let rows := fun j => countedRetainedMaximum t (a j)
  let q := countedOrderStatistic k (fun j => (rows j).1)
  (q.1,q.2 + ∑ j, (rows j).2 + 4)

lemma countedPilot_value (hm : 1≤m) (t : ℝ × ℝ)
    (p : Reservoir n (outerPilotRounds m) × (Fin (outerPilotRounds m) → Fin n → ℝ)) :
    (countedPilot hm t (taggedTrainingRows p.1 p.2)).1 = outerPilotValue m hm t p := by
  have hr := outerPilotRank_pos hm
  unfold countedPilot outerPilotValue numericalPilotOrder retainedPilotSamples
  dsimp only
  rw [countedOrderStatistic_value]
  simp_rw [countedRetainedMaximum_value]
  have he : outerPilotRank m-1+1 = outerPilotRank m := by omega
  congr 1

lemma countedPilot_work {K : Type*} [LinearOrder K] [Zero K] (hm : 1≤m) (t : K × K)
    (a : Fin (outerPilotRounds m) → Fin n → K × K) :
    (countedPilot hm t a).2 ≤ 20*(outerPilotRounds m+1)^2*(n+1) := by
  unfold countedPilot
  dsimp only
  have h := countedOrderStatistic_work (α := K)
    (⟨outerPilotRank m-1, by have := outerPilotRank_pos hm; unfold outerPilotRounds; omega⟩ :
      Fin (outerPilotRounds m)) (fun j => (countedRetainedMaximum t (a j)).1)
  simp only [countedRetainedMaximum_work, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  nlinarith [Nat.zero_le ((outerPilotRounds m)^2*n)]

end ProphetSecretary.Statistics.Calibration
