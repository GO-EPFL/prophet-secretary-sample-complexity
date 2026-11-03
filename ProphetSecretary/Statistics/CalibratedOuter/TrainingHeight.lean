import ProphetSecretary.Statistics.CalibratedOuter.CountedTraining
import ProphetSecretary.Statistics.CalibratedOuter.MeshHeight

/-!
# Rational operands of the outer training statistics

Tagged minima, maxima, and the pilot order statistic choose stored entries.
They do not increase the operand heights. The numerical cap then supplies
the mesh and normalization denominators.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

private lemma countedMaximumFrom_preserves {α : Type*} [LinearOrder α]
    (P : α → Prop) (a : α) (l : List α) (ha : P a) (hl : ∀ x ∈ l, P x) :
    P (countedMaximumFrom a l).1 := by
  induction l generalizing a with
  | nil => exact ha
  | cons b l ih =>
    have hm : P (max a b) := by
      rcases max_choice a b with h | h
      · exact h.symm ▸ ha
      · exact h.symm ▸ hl b List.mem_cons_self
    exact ih (max a b) hm (fun x hx => hl x (List.mem_cons_of_mem _ hx))

private lemma countedFiniteMaximum_preserves {α : Type*} [LinearOrder α] {n : ℕ}
    (P : α → Prop) (hn : 0<n) (f : Fin n → α) (h : ∀ i, P (f i)) : P (countedFiniteMaximum hn f).1 := by
  apply countedMaximumFrom_preserves P (f ⟨0,hn⟩) (List.ofFn f) (h ⟨0,hn⟩)
  intro a ha
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ha
  exact h i

theorem countedCutoff_height {n m : ℕ} (hm : 1 ≤ m) (a : Fin m → Fin n → ℚ × ℚ)
    (Y B : ℕ) (h : ∀ r i, RationalHeight (a r i).1 Y ∧ RationalHeight (a r i).2 B) :
    RationalHeight (countedCutoff hm a).1.1 Y ∧ RationalHeight (countedCutoff hm a).1.2 B := by
  let P := fun t : Lex (ℚ × ℚ) => RationalHeight (ofLex t).1 Y ∧ RationalHeight (ofLex t).2 B
  by_cases hn : 0 < n
  · let row := fun r => (countedFiniteMaximum (α := Lex (ℚ × ℚ)) hn (fun i => toLex (a r i))).1
    have hr (r : Fin m) : P (row r) := countedFiniteMaximum_preserves P hn _ (h r)
    simp only [countedCutoff,dif_pos hn]
    exact countedFiniteMaximum_preserves (α := (Lex (ℚ × ℚ))ᵒᵈ) P (by omega : 0<m) row hr
  · simp only [countedCutoff,dif_neg hn]
    exact ⟨rationalHeight_zero.mono (Nat.zero_le _),rationalHeight_zero.mono (Nat.zero_le _)⟩

lemma countedRetainedMaximum_height {n : ℕ} (t : ℚ × ℚ) (a : Fin n → ℚ × ℚ)
    (Y : ℕ) (h : ∀ i, RationalHeight (a i).1 Y) : RationalHeight (countedRetainedMaximum t a).1 Y := by
  let f := fun i => if (toLex t : Lex (ℚ × ℚ)) < toLex (a i) then (a i).1 else 0
  have hz := rationalHeight_zero.mono (Nat.zero_le Y)
  change RationalHeight (countedMaximumFrom 0 (List.ofFn f)).1 Y
  apply countedMaximumFrom_preserves (fun x => RationalHeight x Y) 0 (List.ofFn f) hz
  intro x hx
  obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx
  unfold f
  split_ifs
  · exact h i
  · exact hz

lemma countedOrderStatistic_height {n : ℕ} (k : Fin n) (x : Fin n → ℚ)
    (Y : ℕ) (h : ∀ i, RationalHeight (x i) Y) : RationalHeight (countedOrderStatistic k x).1 Y := by
  have hm : (countedOrderStatistic k x).1 ∈ (countedInsertionSort (fun a b => b≤a) (List.ofFn x)).1 :=
    List.get_mem _ _
  rw [countedInsertionSort_value,List.mem_insertionSort] at hm
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  rw [← hi]
  exact h i

theorem countedPilot_height {n m : ℕ} (hm : 1≤m) (t : ℚ × ℚ)
    (a : Fin (outerPilotRounds m) → Fin n → ℚ × ℚ) (Y : ℕ)
    (h : ∀ r i, RationalHeight (a r i).1 Y) : RationalHeight (countedPilot hm t a).1 Y :=
  countedOrderStatistic_height _ _ Y (fun r => countedRetainedMaximum_height t (a r) Y (h r))

theorem countedMeshNormalized_height (H x : ℚ) (m B X P : ℕ)
    (hH : RationalHeight H B) (hX : RationalHeight x X) (hm : m ≤ 2^P) :
    RationalHeight ((countedMeshRound H m x).1/H) (2*B+2*P) := by
  have h := (countedMeshRound_operands_height H x m B X P hH hX hm).2.2.2
  exact (h.div hH).mono (by omega)

end ProphetSecretary.Statistics.Calibration
