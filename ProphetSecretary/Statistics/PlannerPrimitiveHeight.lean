import ProphetSecretary.Analysis.MultilevelRationalHeight
import ProphetSecretary.Statistics.ScalarPlannerWorkData
import ProphetSecretary.Statistics.PlannerFairSeed

/-!
# Rational bounds for the empirical planner primitives

On each comparison region the excess sum is a sum of stored values minus a
count times the threshold. This bounds its height additively in the threshold
height even though the scan reads that threshold in several comparisons.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability ArithmeticExpression

variable {n : ℕ}

lemma countedPlannerRowProbability_height (l : List ℚ) (P : ℕ) (hL : l.length ≤ 2^P) :
    RationalHeight (countedPlannerRowProbability l).1 (2*P) := by
  let z := l.countP (fun x => decide (x ≤ 0))
  have hz : z ≤ l.length := List.countP_le_length
  have h : RationalHeight ((l.length-z:ℕ):ℚ) P := rationalHeight_natCast _ _ (Nat.sub_le .. |>.trans hL)
  have hden := rationalHeight_natCast _ _ hL
  simp only [countedPlannerRowProbability, countedRowCDFCounts_value]
  change RationalHeight (((l.length:ℚ)-(z:ℚ))/(l.length:ℚ)) (2*P)
  rw [← Nat.cast_sub hz, two_mul]
  exact h.div hden

lemma countedPlannerWeight_height (p : Fin n → ℚ) (P : ℕ) (hp : ∀ i, RationalHeight (p i) P)
    (l : List (Fin n)) : RationalHeight (countedPlannerWeight p l).1 (l.length*(P+3)) := by
  induction l with
  | nil => simpa only [countedPlannerWeight, List.length_nil, zero_mul] using rationalHeight_one
  | cons i l ih =>
    have h := rationalHeight_one.add (rationalHeight_four.mul (hp i))
    simp only [countedPlannerWeight, List.length_cons]
    apply (h.mul ih).mono
    rw [Nat.add_mul]
    omega

lemma countedPlannerWeight_active_height (p : Fin n → ℚ) (P : ℕ) (hp : ∀ i, RationalHeight (p i) P)
    (l : List (Fin n)) (hl : l.Nodup) :
    RationalHeight (countedPlannerWeight p (countedPlannerActive p l).1).1 (n*(P+3)) := by
  have hlen := Finset.card_le_univ l.toFinset
  rw [List.toFinset_card_of_nodup hl, Fintype.card_fin] at hlen
  exact (countedPlannerWeight_height p P hp _).mono (Nat.mul_le_mul_right _
    ((countedPlannerActive_length p l).trans hlen))

lemma countedPlannerExcessTotals_affine (l : List ℚ) (v : ℚ) (Y : ℕ)
    (hY : ∀ x ∈ l, RationalHeight x Y) :
    ∃ (a : ℚ) (c : ℕ), (countedPlannerExcessTotals v l).1.1 = a - (c:ℚ)*v ∧
      RationalHeight a (l.length*(Y+1)) ∧ c ≤ l.length := by
  induction l with
  | nil => exact ⟨0,0,by simp [countedPlannerExcessTotals], by simpa using rationalHeight_zero, by simp⟩
  | cons x l ih =>
    obtain ⟨a,c,ha,hA,hc⟩ := ih (fun y hy => hY y (List.mem_cons_of_mem _ hy))
    by_cases hx : 0 < x
    · by_cases hv : v ≤ x
      · refine ⟨x+a,c+1,?_,?_,by simp only [List.length_cons]; omega⟩
        · simp only [countedPlannerExcessTotals, hx, if_true, max_eq_right (sub_nonneg.mpr hv), ha, Nat.cast_add, Nat.cast_one]
          ring
        · have h := (hY x List.mem_cons_self).add hA
          apply h.mono
          rw [List.length_cons, Nat.add_mul]
          omega
      · refine ⟨a,c,?_,?_,by simp only [List.length_cons]; omega⟩
        · simp only [countedPlannerExcessTotals, hx, if_true, max_eq_left (sub_nonpos.mpr (le_of_not_ge hv)), zero_add, ha]
        · exact hA.mono (Nat.mul_le_mul_right _ (Nat.le_succ _))
    · refine ⟨a,c,?_,hA.mono (Nat.mul_le_mul_right _ (Nat.le_succ _)),by simp only [List.length_cons]; omega⟩
      simp only [countedPlannerExcessTotals, hx, if_false, ha]

lemma countedPlannerExcess_height (l : List ℚ) (v : ℚ) (Y P A m : ℕ)
    (hY : ∀ x ∈ l, RationalHeight x Y) (hm : l.length ≤ m) (hP : m ≤ 2^P)
    (hv : RationalHeight v A) :
    RationalHeight (countedPlannerExcess l v).1 (m*(Y+1)+2*P+A+1) := by
  obtain ⟨a,c,he,ha,hc⟩ := countedPlannerExcessTotals_affine l v Y hY
  have hC := rationalHeight_natCast c P (hc.trans (hm.trans hP))
  have hcount := rationalHeight_natCast (l.countP (fun x => decide (0 < x))) P
    (List.countP_le_length.trans (hm.trans hP))
  have hD : (countedPlannerExcessTotals v l).1.2 = (l.countP (fun x => decide (0 < x)):ℚ) :=
    congrArg Prod.snd (countedPlannerExcessTotals_value v l)
  simp only [countedPlannerExcess, he, hD]
  have hb := (ha.sub (hC.mul hv)).div hcount
  have hL := Nat.mul_le_mul_right (Y+1) hm
  exact hb.mono (by omega)

lemma countedPlannerFraction_height (l : List (Fin n)) (u : Fin n → ℚ) (b : ℕ)
    (hu : ∀ i, RationalHeight (u i) b) : RationalHeight (countedPlannerFraction l u).1 b := by
  have hMax (l' : List (Fin n)) : RationalHeight (eval u (maximumList l' (fun j => .input j))) b := by
    induction l' with
    | nil => exact rationalHeight_zero.mono (Nat.zero_le _)
    | cons j l' ih =>
      change RationalHeight (max (u j) (eval u (maximumList l' (fun j => .input j)))) b
      exact ((hu j).max ih).mono (max_le le_rfl le_rfl)
  simp only [countedPlannerFraction, countedMaximumExpression_value, eval]
  exact ((hMax l).min rationalHeight_one).mono (max_le le_rfl (Nat.zero_le _))

lemma countedPlannerUniformSampler_fraction_height (l : List (Fin n)) (p : Fin n → ℚ)
    (s : PlannerFieldSeed n ℚ) (b : ℕ) (hs : ∀ i, RationalHeight (s.2.2.1 i) b) :
    RationalHeight (countedPlannerUniformSampler l p s).1.2.1 b := by
  cases l with
  | nil => exact rationalHeight_zero.mono (Nat.zero_le _)
  | cons i l => exact countedPlannerFraction_height _ _ b hs

lemma gridPoint_height (b : ℕ) (j : Fin (2^b)) :
    RationalHeight (gridPoint (K := ℚ) (2^b) j) b := by
  have h := rationalHeight_of_fraction (j.val:ℤ) ((2^b:ℕ):ℤ) (by positivity) b
    (by simpa only [Int.natAbs_natCast] using j.isLt.le) (by simp)
  simpa only [gridPoint, Int.cast_natCast] using h

lemma countedPlannerFairSeed_fraction_height (b : ℕ) (s : PlannerFairSeed n b) (i : Fin n) :
    RationalHeight ((countedPlannerFairSeed b s).1.2.2.1 i) b :=
  gridPoint_height b (countedFairBitsIndex b (s.2.2.1 i)).1

lemma countedScalarPlannerPayoff_height (rows : Vector (List ℚ) n) (p : Fin n → ℚ)
    (o : PlannerListOutput n ℚ) (a : ℚ) (m Y P Pp A : ℕ)
    (hm : ∀ i, (rows.get i).length ≤ m) (hP : m ≤ 2^P)
    (hY : ∀ i q, q ∈ rows.get i → RationalHeight q Y) (hp : ∀ i, RationalHeight (p i) Pp)
    (ho : o.2.2.Nodup) (ha : RationalHeight a A) :
    RationalHeight (countedScalarPlannerPayoff rows p o a).1
      (2*(n*(Pp+3))+m*(Y+1)+2*P+1+A) := by
  cases h : o.1 with
  | none =>
    simp only [countedScalarPlannerPayoff, h]
    exact rationalHeight_zero.mono (Nat.zero_le _)
  | some i =>
    let q := (countedPlannerWeight p (countedPlannerActive p o.2.2).1).1
    have hq := countedPlannerWeight_active_height p Pp hp o.2.2 ho
    have hv : RationalHeight (q*a) (n*(Pp+3)+A) := hq.mul ha
    have hx := countedPlannerExcess_height (rows.get i) (q*a) Y P _ m (hY i) (hm i) hP hv
    simp only [countedScalarPlannerPayoff, h]
    exact (hx.div hq).mono (by omega)

end ProphetSecretary.Statistics
