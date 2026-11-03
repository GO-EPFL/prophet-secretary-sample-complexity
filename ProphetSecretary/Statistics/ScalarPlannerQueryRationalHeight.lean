import ProphetSecretary.Statistics.ScalarPlannerRationalHeight
import ProphetSecretary.Statistics.ScalarPlannerRationalFairQuery

/-!
# Rational size of the complete scalar query

The stored probabilities have height at most twice the row-count height.
The median selects one of the evaluated copies, and clipping uses fixed
integer constants.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ}

lemma plannerProbabilityRead_height (rows : Vector (List ℚ) n) (m P : ℕ)
    (hm : ∀ i, (rows.get i).length ≤ m) (hP : m ≤ 2^P) (i : Fin n) :
    RationalHeight (plannerProbabilityRead (countedPlannerProbabilities rows).1 i) (2*P) := by
  simpa [plannerProbabilityRead,countedPlannerProbabilities,Vector.get] using
    countedPlannerRowProbability_height (rows.get i) P ((hm i).trans hP)

lemma sortedMedian_rationalHeight (c B : ℕ) (x : Fin (2*c+1) → ℚ)
    (hx : ∀ i, RationalHeight (x i) B) : RationalHeight (sortedMedian c x) B := by
  have hm : sortedMedian c x ∈ List.insertionSort (fun a b => b≤a) (List.ofFn x) := List.get_mem _ _
  rw [List.mem_insertionSort] at hm
  obtain ⟨i,hi⟩ := List.mem_ofFn.mp hm
  rw [← hi]
  exact hx i

theorem countedScalarPlannerQueryAtLevel_fair_height (rows : Vector (List ℚ) n)
    (m Y P U Z b r : ℕ) (hm : ∀ i, (rows.get i).length ≤ m) (hP : m ≤ 2^P)
    (hY : ∀ i q, q ∈ rows.get i → RationalHeight q Y) (hZ : 2 ≤ Z)
    (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup)
    (hu : RationalHeight x.2.1 U) (hz : RationalHeight x.2.2 Z)
    (pFail : ℚ) (H : ∃ j : ℕ, (1/4 : ℚ)^j ≤ pFail)
    (bits : Fin (confidenceCopyCount pFail H) → MultilevelTree (PlannerFairSeed n b) r) :
    RationalHeight (countedScalarPlannerQueryAtLevel rows x r pFail H
      (fun i => multilevelTreeMap (fun s => (countedPlannerFairSeed b s).1) r (bits i))).value
      (n*(2*P+3)+64*(plannerPrimitiveHeight n m Y P (2*P) U Z b r+r+1)*16^r+3) := by
  let p := plannerProbabilityRead (countedPlannerProbabilities rows).1
  let f := (countedScalarPlannerFrame p x).1
  let s := fun i => multilevelTreeMap (fun z => (countedPlannerFairSeed b z).1) r (bits i)
  let C := 64*(plannerPrimitiveHeight n m Y P (2*P) U Z b r+r+1)*16^r
  let B := n*(2*P+3)+C
  have hp := plannerProbabilityRead_height rows m P hm hP
  have hF := countedScalarPlannerFrame_height p (2*P) U Z hp x hx hu hz hZ
  have hC (i : Fin (confidenceCopyCount pFail H)) :
      RationalHeight (countedScalarPlannerSinglePrepared rows p f.weight x r (s i)).1 B :=
    hF.2.2.1.mul (countedScalarPlannerRecursion_fair_height rows p m Y P (2*P) U Z b r
      hm hP hY hp hZ x hx hu hz (bits i))
  unfold countedScalarPlannerQueryAtLevel
  change RationalHeight ((if f.active.isEmpty then _ else _ : MedianCopiesResult ℚ).value) (B+3)
  by_cases he : f.active.isEmpty = true
  · rw [if_pos he]
    apply hF.2.2.2.1.mono
    have h16 : 1 ≤ 16^r := Nat.succ_le_of_lt (by positivity)
    have h := Nat.le_mul_of_pos_right (64*(plannerPrimitiveHeight n m Y P (2*P) U Z b r+r+1)) h16
    dsimp [B,C,plannerPrimitiveHeight] at h ⊢
    omega
  · rw [if_neg he]
    change RationalHeight (clipFive (confidenceMedianCopies pFail H
      (countedScalarPlannerSinglePrepared rows p f.weight x r) s).value) (B+3)
    rw [confidenceMedianCopies_value]
    exact (rationalHeight_clipFive (sortedMedian_rationalHeight _ B _ hC)).mono (max_le (by omega) (by omega))

theorem countedRationalFairQueryAtLevel_height (rows : Vector (List ℚ) n)
    (m Y P U Z b r : ℕ) (hm : ∀ i, (rows.get i).length ≤ m) (hP : m ≤ 2^P)
    (hY : ∀ i q, q ∈ rows.get i → RationalHeight q Y) (hZ : 2 ≤ Z)
    (x : ScalarPlannerListState n ℚ) (hx : x.1.Nodup)
    (hu : RationalHeight x.2.1 U) (hz : RationalHeight x.2.2 Z)
    (pFail : ℚ) (H : ∃ j : ℕ, (1/4 : ℚ)^j ≤ pFail)
    (bits : Fin (confidenceCopyCount pFail H) → MultilevelTree (PlannerFairSeed n b) r) :
    RationalHeight (countedRationalFairQueryAtLevel rows x r pFail H b bits).value
      (n*(2*P+3)+64*(plannerPrimitiveHeight n m Y P (2*P) U Z b r+r+1)*16^r+3) := by
  simp only [countedRationalFairQueryAtLevel,countedStoredPlannerFairSeed_value]
  exact countedScalarPlannerQueryAtLevel_fair_height rows m Y P U Z b r hm hP hY hZ x hx hu hz pFail H bits

end ProphetSecretary.Statistics
