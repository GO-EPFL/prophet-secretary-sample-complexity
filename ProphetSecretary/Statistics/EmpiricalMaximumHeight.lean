import ProphetSecretary.Statistics.EmpiricalMaximumWork
import ProphetSecretary.Analysis.RationalHeight

/-!
# Rational sizes in the empirical maximum computation

Each marginal CDF is a ratio of two row counts. The maximum calculation
multiplies these ratios and sums the resulting support atom contributions.
The bounds also apply to the suffix accumulators of the actual scans.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis

lemma countedRowCDFCounts_height (l : List ℚ) (a : ℚ) (P : ℕ) (hL : l.length ≤ 2^P) :
    RationalHeight (countedRowCDFCounts l a).1.1.1 P ∧
      RationalHeight (countedRowCDFCounts l a).1.1.2 P ∧
      RationalHeight (countedRowCDFCounts l a).1.2 P := by
  rw [countedRowCDFCounts_value]
  exact ⟨rationalHeight_natCast _ _ (List.countP_le_length.trans hL),
    rationalHeight_natCast _ _ (List.countP_le_length.trans hL),rationalHeight_natCast _ _ hL⟩

lemma countedRowCDF_height (l : List ℚ) (a : ℚ) (P : ℕ) (hL : l.length ≤ 2^P) :
    RationalHeight (countedRowCDF l a).1.1 (P+P) ∧ RationalHeight (countedRowCDF l a).1.2 (P+P) := by
  have h := countedRowCDFCounts_height l a P hL
  exact ⟨h.1.div h.2.2,h.2.1.div h.2.2⟩

theorem countedCDFProducts_height (rows : List (List ℚ)) (a : ℚ) (P : ℕ)
    (hL : ∀ r ∈ rows, r.length ≤ 2^P) :
    RationalHeight (countedCDFProducts rows a).1.1 ((P+P)*rows.length) ∧
      RationalHeight (countedCDFProducts rows a).1.2 ((P+P)*rows.length) := by
  induction rows with
  | nil => exact ⟨rationalHeight_one,rationalHeight_one⟩
  | cons r rows ih =>
    have hR := countedRowCDF_height r a P (hL r List.mem_cons_self)
    have hT := ih (fun q hq => hL q (List.mem_cons_of_mem _ hq))
    constructor
    · exact (hR.1.mul hT.1).mono (by simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega)
    · exact (hR.2.mul hT.2).mono (by simp only [List.length_cons,Nat.mul_add,Nat.mul_one]; omega)

lemma countedEmpiricalSupport_height (rows : List (List ℚ)) (Y : ℕ)
    (hY : ∀ a ∈ rows.flatten, RationalHeight a Y) (a : ℚ) (ha : a ∈ (countedEmpiricalSupport rows).1) :
    RationalHeight a Y := by
  rcases (countedEmpiricalSupport_mem rows a).mp ha with he | ⟨h,_⟩
  · rw [he]
    exact rationalHeight_zero.mono (Nat.zero_le _)
  · exact hY a h

theorem countedEmpiricalAtom_height (rows : List (List ℚ)) (a : ℚ) (P Y : ℕ)
    (hP : ∀ r ∈ rows, r.length ≤ 2^P) (ha : RationalHeight a Y) :
    RationalHeight ((countedCDFProducts rows a).1.1-(countedCDFProducts rows a).1.2)
        (4*P*rows.length+1) ∧
      RationalHeight (a*((countedCDFProducts rows a).1.1-(countedCDFProducts rows a).1.2))
        (Y+4*P*rows.length+1) := by
  have h := countedCDFProducts_height rows a P hP
  have hE : (P+P)*rows.length+(P+P)*rows.length+1 = 4*P*rows.length+1 := by ring
  have hD := (h.1.sub h.2).mono hE.le
  exact ⟨hD,(ha.mul hD).mono (by omega)⟩

theorem countedEmpiricalAtoms_height (support : List ℚ) (rows : List (List ℚ)) (P Y : ℕ)
    (hP : ∀ r ∈ rows, r.length ≤ 2^P) (hY : ∀ a ∈ support, RationalHeight a Y) :
    RationalHeight (countedEmpiricalAtoms support rows).1 (support.length*(Y+4*P*rows.length+2)) := by
  let C := Y+4*P*rows.length+2
  induction support with
  | nil => simpa only [countedEmpiricalAtoms,List.length_nil,zero_mul] using rationalHeight_zero
  | cons a l ih =>
    have hA := (countedEmpiricalAtom_height rows a P Y hP (hY a List.mem_cons_self)).2
    have hL := ih (fun q hq => hY q (List.mem_cons_of_mem _ hq))
    have h : RationalHeight (a*((countedCDFProducts rows a).1.1-(countedCDFProducts rows a).1.2)+
        (countedEmpiricalAtoms l rows).1) ((Y+4*P*rows.length+1)+l.length*C+1) := hA.add hL
    exact h.mono (by change _ ≤ (l.length+1)*C; rw [Nat.add_mul,Nat.one_mul]; dsimp [C]; omega)

theorem countedEmpiricalMaximum_height (rows : List (List ℚ)) (P Y : ℕ)
    (hP : ∀ r ∈ rows, r.length ≤ 2^P) (hY : ∀ a ∈ rows.flatten, RationalHeight a Y) :
    RationalHeight (countedEmpiricalMaximum rows).1 ((rows.flatten.length+1)*(Y+4*P*rows.length+2)) :=
  (countedEmpiricalAtoms_height (countedEmpiricalSupport rows).1 rows P Y hP
    (countedEmpiricalSupport_height rows Y hY)).mono
      (Nat.mul_le_mul_right _ (countedEmpiricalSupport_length rows))

end ProphetSecretary.Statistics
