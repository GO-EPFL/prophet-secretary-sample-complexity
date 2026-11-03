import ProphetSecretary.Statistics.ScalarPlannerValueMap

/-!
# Confidence queries under an ordered field embedding

The confidence search, sorting median, and clipping preserve the value
interpretation. The finite copy arrays have the same shape on both sides.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ} {K L : Type*} [Field K] [Field L] [LinearOrder K] [LinearOrder L]
  [IsStrictOrderedRing K] [IsStrictOrderedRing L]

variable (f : K →+* L) (hf : StrictMono f)
include hf

omit [LinearOrder K] [LinearOrder L] [IsStrictOrderedRing K] [IsStrictOrderedRing L] hf in
private lemma quarterPower_valueMap (j : ℕ) : f ((1/4:K)^j)=(1/4:L)^j := by
  simp only [map_pow,map_div₀,map_one,map_ofNat]

lemma confidenceLevel_valueMap (p : K) (H : ∃ j : ℕ, (1/4:K)^j≤p)
    (H' : ∃ j : ℕ, (1/4:L)^j≤f p) : countedConfidenceLevel (f p) H'=countedConfidenceLevel p H := by
  have h (j : ℕ) : (1/4:L)^j≤f p ↔ (1/4:K)^j≤p := by
    rw [← quarterPower_valueMap f j,hf.le_iff_le]
  have he : Nat.find H'=Nat.find H := le_antisymm
    (Nat.find_min' H' ((h _).mpr (Nat.find_spec H))) (Nat.find_min' H ((h _).mp (Nat.find_spec H')))
  apply Prod.ext
  · simp only [(countedConfidenceLevel_spec _ _).1,he]
  · simp only [(countedConfidenceLevel_spec _ _).2,he]

lemma confidenceCopies_valueMap (p : K) (H : ∃ j : ℕ, (1/4:K)^j≤p)
    (H' : ∃ j : ℕ, (1/4:L)^j≤f p) : confidenceCopyCount (f p) H'=confidenceCopyCount p H := by
  simp only [confidenceCopyCount,confidenceLevel_valueMap f hf p H H']

omit [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
lemma sortedMedian_valueMap (c : ℕ) (x : Fin (2*c+1) → K) :
    sortedMedian c (fun i => f (x i)) = f (sortedMedian c x) := by
  have hsort : (List.insertionSort (fun a b : K => b≤a) (List.ofFn x)).map f =
      List.insertionSort (fun a b : L => b≤a) (List.ofFn (fun i => f (x i))) := by
    rw [List.map_insertionSort (r := fun a b : K => b≤a) (s := fun a b : L => b≤a)
      _ _ (fun a _ b _ => hf.le_iff_le.symm)]
    simp [List.map_ofFn,Function.comp_def]
  unfold sortedMedian
  have h := congrArg (fun l : List L => l[c]?) hsort
  have hK : c < (List.insertionSort (fun a b : K => b≤a) (List.ofFn x)).length := by
    simp only [List.length_insertionSort,List.length_ofFn]; omega
  have hL : c < (List.insertionSort (fun a b : L => b≤a) (List.ofFn (fun i => f (x i)))).length := by
    simp only [List.length_insertionSort,List.length_ofFn]; omega
  simpa only [List.get_eq_getElem,List.getElem?_map,List.getElem?_eq_getElem hK,
    List.getElem?_eq_getElem hL,Option.map_some,Option.some.injEq] using h.symm

omit [IsStrictOrderedRing K] [IsStrictOrderedRing L] in
private lemma sortedMedian_valueMap_index {a b : ℕ} (h : b=a) (x : Fin (2*a+1) → K) :
    sortedMedian b (fun i => f (x (Fin.cast (congrArg (fun c => 2*c+1) h) i))) = f (sortedMedian a x) := by
  subst b
  exact sortedMedian_valueMap f hf a x

theorem countedScalarPlannerQueryAtLevel_valueMap (rows : Vector (List K) n) (x : ScalarPlannerListState n K)
    (r : ℕ) (p : K) (H : ∃ j : ℕ, (1/4:K)^j≤p) (H' : ∃ j : ℕ, (1/4:L)^j≤f p)
    (s : Fin (confidenceCopyCount p H) → MultilevelTree (PlannerFieldSeed n K) r) :
    (countedScalarPlannerQueryAtLevel (plannerRowsValueMap f rows) (scalarPlannerStateValueMap f x)
      r (f p) H' (fun i => multilevelTreeMap (plannerMapSeed f) r
        (s (Fin.cast (confidenceCopies_valueMap f hf p H H') i)))).value =
      f (countedScalarPlannerQueryAtLevel rows x r p H s).value := by
  let probs := plannerProbabilityRead (countedPlannerProbabilities rows).1
  let frame := (countedScalarPlannerFrame probs x).1
  have hP : plannerProbabilityRead (countedPlannerProbabilities (plannerRowsValueMap f rows)).1 =
      fun i => f (probs i) := funext (plannerProbabilityRead_valueMap f hf rows)
  have hf' : (countedScalarPlannerFrame (plannerProbabilityRead (countedPlannerProbabilities
      (plannerRowsValueMap f rows)).1) (scalarPlannerStateValueMap f x)).1 = scalarPlannerFrameValueMap f frame := by
    rw [hP,countedScalarPlannerFrame_valueMap f hf]
  have hSingle (t : MultilevelTree (PlannerFieldSeed n K) r) :
      (countedScalarPlannerSinglePrepared (plannerRowsValueMap f rows) (fun i => f (probs i)) (f frame.weight)
        (scalarPlannerStateValueMap f x) r (multilevelTreeMap (plannerMapSeed f) r t)).1 =
      f (countedScalarPlannerSinglePrepared rows probs frame.weight x r t).1 := by
    simp only [countedScalarPlannerSinglePrepared,map_mul,countedScalarPlannerEstimate_valueMap f hf]
  have hClip (a : K) : f (clipFive a)=clipFive (f a) := by
    simp [clipFive,hf.monotone.map_max,hf.monotone.map_min,map_ofNat]
  unfold countedScalarPlannerQueryAtLevel
  dsimp only
  by_cases h : frame.active.isEmpty = true
  · rw [hf']
    change (if frame.active.isEmpty then _ else _ : MedianCopiesResult L).value =
      f ((if frame.active.isEmpty then _ else _ : MedianCopiesResult K).value)
    simp only [h,if_true]
    rfl
  · rw [hf']
    change (if frame.active.isEmpty then _ else _ : MedianCopiesResult L).value =
      f ((if frame.active.isEmpty then _ else _ : MedianCopiesResult K).value)
    simp only [if_neg h,confidenceMedianCopies_value,hClip]
    apply congrArg clipFive
    simp only [scalarPlannerFrameValueMap,hP,hSingle]
    exact sortedMedian_valueMap_index f hf (congrArg Prod.fst (confidenceLevel_valueMap f hf p H H'))
      (fun i => (countedScalarPlannerSinglePrepared rows probs frame.weight x r (s i)).1)

end ProphetSecretary.Statistics
