import ProphetSecretary.Statistics.ScalarPlannerRational
import ProphetSecretary.Statistics.ScalarPlannerWorkQuery

/-!
# Rational accuracy and confidence queries

The rational and real searches choose the same level and number of
copies. The rational median and clipping agree with their real values.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ}

private lemma quarter_pow_ratCast (j : ℕ) : (((1/4 : ℚ)^j : ℚ) : ℝ) = (1/4 : ℝ)^j := by
  simp only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]

lemma quarter_pow_le_ratCast (p : ℚ) (j : ℕ) : (1/4 : ℝ)^j ≤ (p : ℝ) ↔ (1/4 : ℚ)^j ≤ p := by
  rw [← quarter_pow_ratCast, Rat.cast_le]

lemma exists_quarter_pow_le_ratCast (p : ℚ) :
    (∃ j : ℕ, (1/4 : ℝ)^j ≤ (p : ℝ)) ↔ (∃ j : ℕ, (1/4 : ℚ)^j ≤ p) :=
  exists_congr (quarter_pow_le_ratCast p)

private lemma quarter_find_ratCast (p : ℚ)
    (Hq : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p) (Hr : ∃ j : ℕ, (1/4 : ℝ)^j ≤ (p : ℝ)) :
    Nat.find Hr = Nat.find Hq := by
  apply le_antisymm
  · exact Nat.find_min' Hr ((quarter_pow_le_ratCast p _).mpr (Nat.find_spec Hq))
  · exact Nat.find_min' Hq ((quarter_pow_le_ratCast p _).mp (Nat.find_spec Hr))

lemma countedConfidenceLevel_ratCast (p : ℚ)
    (Hq : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p) (Hr : ∃ j : ℕ, (1/4 : ℝ)^j ≤ (p : ℝ)) :
    countedConfidenceLevel (p : ℝ) Hr = countedConfidenceLevel p Hq := by
  apply Prod.ext
  · simp only [(countedConfidenceLevel_spec _ _).1, quarter_find_ratCast p Hq Hr]
  · simp only [(countedConfidenceLevel_spec _ _).2, quarter_find_ratCast p Hq Hr]

lemma confidenceCopyCount_ratCast (p : ℚ)
    (Hq : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p) (Hr : ∃ j : ℕ, (1/4 : ℝ)^j ≤ (p : ℝ)) :
    confidenceCopyCount (p : ℝ) Hr = confidenceCopyCount p Hq := by
  simp only [confidenceCopyCount, countedConfidenceLevel_ratCast p Hq Hr]

lemma scalarPlannerPrecisionRatio_ratCast (β h : ℚ) :
    scalarPlannerPrecisionRatio (β : ℝ) (h : ℝ) = ((scalarPlannerPrecisionRatio β h : ℚ) : ℝ) := by
  simp only [scalarPlannerPrecisionRatio, Rat.cast_pow, Rat.cast_div, Rat.cast_mul, Rat.cast_ofNat]

private lemma countedProbabilityFunction_ratCast (rows : Vector (List ℚ) n) :
    plannerProbabilityRead (countedPlannerProbabilities (plannerRowsRatCast rows)).1 =
      fun i => ((plannerProbabilityRead (countedPlannerProbabilities rows).1 i : ℚ) : ℝ) := by
  funext i
  exact plannerProbabilityRead_ratCast rows i

lemma storedScalarPlannerWeight_ratCast (rows : Vector (List ℚ) n) (x : ScalarPlannerListState n ℚ) :
    storedScalarPlannerWeight (plannerRowsRatCast rows) (scalarPlannerStateRatCast x) =
      ((storedScalarPlannerWeight rows x : ℚ) : ℝ) := by
  simp only [storedScalarPlannerWeight, countedProbabilityFunction_ratCast, countedScalarPlannerFrame_ratCast]
  rfl

lemma countedScalarPlannerLevel_ratCast (β h : ℚ)
    (Hq : ∃ j : ℕ, (1/4 : ℚ)^j ≤ scalarPlannerPrecisionRatio β h)
    (Hr : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio (β : ℝ) (h : ℝ)) :
    (countedScalarPlannerLevel (β : ℝ) (h : ℝ) Hr).1 = (countedScalarPlannerLevel β h Hq).1 := by
  rw [countedScalarPlannerLevel_value, countedScalarPlannerLevel_value]
  have he : Nat.find Hr = Nat.find Hq := by
    apply le_antisymm
    · apply Nat.find_min' Hr
      rw [scalarPlannerPrecisionRatio_ratCast, quarter_pow_le_ratCast]
      exact Nat.find_spec Hq
    · apply Nat.find_min' Hq
      apply (quarter_pow_le_ratCast _ _).mp
      rw [← scalarPlannerPrecisionRatio_ratCast]
      exact Nat.find_spec Hr
  rw [he, scalarPlannerPrecisionRatio_ratCast]
  have hc (j : ℕ) : 2*(1/4 : ℝ)^j = (((2*(1/4 : ℚ)^j : ℚ)) : ℝ) := by
    rw [Rat.cast_mul, quarter_pow_ratCast]
    norm_num
  rw [hc]
  simp only [Rat.cast_le]

private lemma sortedMedian_ratCast (c : ℕ) (x : Fin (2*c+1) → ℚ) :
    sortedMedian c (fun i => (x i : ℝ)) = ((sortedMedian c x : ℚ) : ℝ) := by
  have hsort : (List.insertionSort (fun a b : ℚ => b ≤ a) (List.ofFn x)).map (fun a : ℚ => (a : ℝ)) =
      List.insertionSort (fun a b : ℝ => b ≤ a) (List.ofFn (fun i => (x i : ℝ))) := by
    calc
      _ = ((List.ofFn x).map (fun a : ℚ => (a : ℝ))).insertionSort (fun a b : ℝ => b ≤ a) :=
        List.map_insertionSort (r := fun a b : ℚ => b ≤ a) (s := fun a b : ℝ => b ≤ a)
          _ _ (fun a _ b _ => Rat.cast_le.symm)
      _ = _ := by simp [List.map_ofFn, Function.comp_def]
  unfold sortedMedian
  have h := congrArg (fun l : List ℝ => l[c]?) hsort
  have hq : c < (List.insertionSort (fun a b : ℚ => b ≤ a) (List.ofFn x)).length := by
    simp only [List.length_insertionSort, List.length_ofFn]; omega
  have hr : c < (List.insertionSort (fun a b : ℝ => b ≤ a)
      (List.ofFn fun i => (x i : ℝ))).length := by
    simp only [List.length_insertionSort, List.length_ofFn]; omega
  simpa only [List.get_eq_getElem, List.getElem?_map, List.getElem?_eq_getElem hq,
    List.getElem?_eq_getElem hr, Option.map_some, Option.some.injEq] using h.symm

private lemma sortedMedian_ratCast_index {a b : ℕ} (hab : b = a) (x : Fin (2*a+1) → ℚ) :
    sortedMedian b (fun i => (x (Fin.cast (congrArg (fun z => 2*z+1) hab) i) : ℝ)) =
      ((sortedMedian a x : ℚ) : ℝ) := by
  subst b
  exact sortedMedian_ratCast a x

lemma countedScalarPlannerSinglePrepared_ratCast (rows : Vector (List ℚ) n) (p : Fin n → ℚ)
    (β : ℚ) (x : ScalarPlannerListState n ℚ) (r : ℕ) (t : MultilevelTree (PlannerFieldSeed n ℚ) r) :
    (countedScalarPlannerSinglePrepared (plannerRowsRatCast rows) (fun i => (p i : ℝ)) (β : ℝ)
      (scalarPlannerStateRatCast x) r (multilevelTreeMap plannerFieldSeedRatCast r t)).1 =
      ((countedScalarPlannerSinglePrepared rows p β x r t).1 : ℝ) := by
  simp only [countedScalarPlannerSinglePrepared, Rat.cast_mul, countedScalarPlannerEstimate_ratCast]

/-- Equality of the computed confidence medians, with the same trees and
the same copy indices on the two sides. -/
theorem countedScalarPlannerQueryAtLevel_ratCast
    (rows : Vector (List ℚ) n) (x : ScalarPlannerListState n ℚ) (r : ℕ) (p : ℚ)
    (Hq : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p) (Hr : ∃ j : ℕ, (1/4 : ℝ)^j ≤ (p : ℝ))
    (seed : Fin (confidenceCopyCount p Hq) → MultilevelTree (PlannerFieldSeed n ℚ) r) :
    (countedScalarPlannerQueryAtLevel (plannerRowsRatCast rows) (scalarPlannerStateRatCast x)
      r (p : ℝ) Hr (fun i => multilevelTreeMap plannerFieldSeedRatCast r
        (seed (Fin.cast (confidenceCopyCount_ratCast p Hq Hr) i)))).value =
      ((countedScalarPlannerQueryAtLevel rows x r p Hq seed).value : ℝ) := by
  let probs := plannerProbabilityRead (countedPlannerProbabilities rows).1
  let frame := (countedScalarPlannerFrame probs x).1
  have hf : (countedScalarPlannerFrame (plannerProbabilityRead (countedPlannerProbabilities
      (plannerRowsRatCast rows)).1) (scalarPlannerStateRatCast x)).1 = scalarPlannerFrameRatCast frame := by
    simp only [countedProbabilityFunction_ratCast, countedScalarPlannerFrame_ratCast, frame, probs]
  unfold countedScalarPlannerQueryAtLevel
  dsimp only
  by_cases h : frame.active.isEmpty = true
  · rw [hf]
    change (if frame.active.isEmpty then _ else _ : MedianCopiesResult ℝ).value =
      (((if frame.active.isEmpty then _ else _ : MedianCopiesResult ℚ).value : ℚ) : ℝ)
    simp only [h, if_true]
    rfl
  · rw [hf]
    change (if frame.active.isEmpty then _ else _ : MedianCopiesResult ℝ).value =
      (((if frame.active.isEmpty then _ else _ : MedianCopiesResult ℚ).value : ℚ) : ℝ)
    simp only [if_neg h, confidenceMedianCopies_value]
    rw [show ∀ a : ℚ, (((clipFive a : ℚ)) : ℝ) = clipFive (a : ℝ) by
      intro a; simp [clipFive, Rat.cast_max, Rat.cast_min]]
    apply congrArg clipFive
    simp only [scalarPlannerFrameRatCast, countedProbabilityFunction_ratCast,
      countedScalarPlannerSinglePrepared_ratCast]
    exact sortedMedian_ratCast_index (congrArg Prod.fst (countedConfidenceLevel_ratCast p Hq Hr))
      (fun i => (countedScalarPlannerSinglePrepared rows probs frame.weight x r (seed i)).1)

lemma countedStoredScalarPlannerLevel_ratCast
    (rows : Vector (List ℚ) n) (x : ScalarPlannerListState n ℚ) (h : ℚ)
    (Hq : ∃ j : ℕ, (1/4 : ℚ)^j ≤ scalarPlannerPrecisionRatio (storedScalarPlannerWeight rows x) h)
    (Hr : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio
      (storedScalarPlannerWeight (plannerRowsRatCast rows) (scalarPlannerStateRatCast x)) (h : ℝ)) :
    (countedScalarPlannerLevel (storedScalarPlannerWeight (plannerRowsRatCast rows) (scalarPlannerStateRatCast x))
      (h : ℝ) Hr).1 = (countedScalarPlannerLevel (storedScalarPlannerWeight rows x) h Hq).1 := by
  generalize he : storedScalarPlannerWeight (plannerRowsRatCast rows) (scalarPlannerStateRatCast x) = β at Hr ⊢
  rw [storedScalarPlannerWeight_ratCast] at he
  subst β
  exact countedScalarPlannerLevel_ratCast _ _ Hq Hr

end ProphetSecretary.Statistics
