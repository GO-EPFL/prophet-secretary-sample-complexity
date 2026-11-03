import ProphetSecretary.Statistics.CalibratedOuter.Work

/-!
# Exact rational outer preprocessing and display

Casting an input rational to the real model preserves each tagged comparison,
the cutoff and pilot, and the downward mesh. The native outer execution
therefore uses only rational arithmetic on the observations it receives.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration

variable {n m : ℕ}

def castOuterPair (t : ℚ × ℚ) : ℝ × ℝ := (t.1,t.2)

private def castOuterLex (t : Lex (ℚ × ℚ)) : Lex (ℝ × ℝ) := toLex (castOuterPair (ofLex t))

private lemma castOuterLex_le (a b : Lex (ℚ × ℚ)) :
    castOuterLex a≤castOuterLex b ↔ a≤b := by
  rw [Prod.Lex.le_iff,Prod.Lex.le_iff]
  simp [castOuterLex,castOuterPair,Rat.cast_le,Rat.cast_lt]

private lemma castOuterLex_lt (a b : Lex (ℚ × ℚ)) :
    castOuterLex a<castOuterLex b ↔ a<b := by
  rw [lt_iff_not_ge,lt_iff_not_ge,castOuterLex_le]

private lemma countedFiniteMaximum_map {A B : Type*} [LinearOrder A] [LinearOrder B]
    (f : A → B) (hf : Monotone f) (hn : 0<n) (x : Fin n → A) :
    (countedFiniteMaximum hn (f ∘ x)).1=f (countedFiniteMaximum hn x).1 := by
  rw [countedFiniteMaximum_value,countedFiniteMaximum_value]
  exact (Finset.apply_sup'_eq_sup'_comp _ f (fun a b => hf.map_sup a b)).symm

private lemma countedFiniteMinimum_map {A B : Type*} [LinearOrder A] [LinearOrder B]
    (f : A → B) (hf : Monotone f) (hn : 0<n) (x : Fin n → A) :
    (countedFiniteMinimum hn (f ∘ x)).1=f (countedFiniteMinimum hn x).1 := by
  rw [countedFiniteMinimum_value,countedFiniteMinimum_value]
  exact (Finset.apply_inf'_eq_inf'_comp _ f (fun a b => hf.map_inf a b)).symm

theorem countedCutoff_ratCast (hm : 1≤m) (a : Fin m → Fin n → ℚ × ℚ) :
    (countedCutoff hm (fun r i => castOuterPair (a r i))).1=
      castOuterPair (countedCutoff hm a).1 := by
  unfold countedCutoff
  split_ifs with hn
  · dsimp only
    have hf : Monotone castOuterLex := fun a b h => (castOuterLex_le a b).mpr h
    have hRow (r : Fin m) :
        (countedFiniteMaximum hn (fun i => toLex (castOuterPair (a r i)))).1 =
          castOuterLex (countedFiniteMaximum hn (fun i => toLex (a r i))).1 :=
      countedFiniteMaximum_map castOuterLex hf hn _
    simp_rw [hRow]
    exact congrArg ofLex (countedFiniteMinimum_map castOuterLex hf (by omega : 0<m) _)
  · norm_num [castOuterPair]

private lemma countedMaximumFrom_ratCast (a : ℚ) (l : List ℚ) :
    (countedMaximumFrom (a : ℝ) (l.map fun q : ℚ => (q : ℝ))).1 =
      ((countedMaximumFrom a l).1 : ℝ) := by
  induction l generalizing a with
  | nil => rfl
  | cons b l ih => simp only [List.map_cons,countedMaximumFrom,← Rat.cast_max,ih]

theorem countedRetention_ratCast (t z : ℚ × ℚ) :
    countedRetention (castOuterPair t) (castOuterPair z) = ((countedRetention t z : ℚ) : ℝ) := by
  have h : ((toLex (castOuterPair t) : Lex (ℝ × ℝ)) < toLex (castOuterPair z)) ↔
      (toLex t : Lex (ℚ × ℚ)) < toLex z := castOuterLex_lt _ _
  unfold countedRetention
  by_cases hp : (toLex t : Lex (ℚ × ℚ)) < toLex z
  · rw [if_pos (h.mpr hp),if_pos hp]
    rfl
  · rw [if_neg (mt h.mp hp),if_neg hp,Rat.cast_zero]

theorem countedRetainedMaximum_ratCast (t : ℚ × ℚ) (a : Fin n → ℚ × ℚ) :
    (countedRetainedMaximum (castOuterPair t) (fun i => castOuterPair (a i))).1 =
      ((countedRetainedMaximum t a).1 : ℝ) := by
  let q : Fin n → ℚ := fun i => countedRetention t (a i)
  change (countedMaximumFrom 0 (List.ofFn (fun i =>
    countedRetention (castOuterPair t) (castOuterPair (a i))))).1 = ((countedMaximumFrom 0 (List.ofFn q)).1 : ℝ)
  simp_rw [countedRetention_ratCast]
  rw [← show (List.ofFn q).map (fun a : ℚ => (a : ℝ)) = List.ofFn (fun i => (q i : ℝ)) by
    simp only [List.map_ofFn,Function.comp_def]]
  simpa only [Rat.cast_zero] using countedMaximumFrom_ratCast 0 (List.ofFn q)

private lemma countedOrderStatistic_sorted {A : Type*} [LinearOrder A] {N : ℕ}
    (k : Fin N) (x : Fin N → A) :
    (ProphetSecretary.Probability.countedOrderStatistic k x).1 =
      (List.insertionSort (fun a b : A => b≤a) (List.ofFn x)).get
        ⟨k.val, by rw [List.length_insertionSort,List.length_ofFn]; exact k.isLt⟩ := by
  let r := fun a b : A => b≤a
  let c := (ProphetSecretary.Probability.countedInsertionSort r (List.ofFn x)).1
  let s := List.insertionSort r (List.ofFn x)
  have h : c=s := ProphetSecretary.Probability.countedInsertionSort_value _ _
  have hc : k.val<c.length := by rw [h]; simpa only [s,List.length_insertionSort,List.length_ofFn] using k.isLt
  have hs : k.val<s.length := by simpa only [s,List.length_insertionSort,List.length_ofFn] using k.isLt
  have he := congrArg (fun l : List A => l[k.val]?) h
  rw [List.getElem?_eq_getElem hc,List.getElem?_eq_getElem hs] at he
  exact Option.some.inj he

private lemma countedOrderStatistic_ratCast {N : ℕ} (k : Fin N) (x : Fin N → ℚ) :
    (ProphetSecretary.Probability.countedOrderStatistic k (fun i => (x i : ℝ))).1 =
      ((ProphetSecretary.Probability.countedOrderStatistic k x).1 : ℝ) := by
  have hsort : (List.insertionSort (fun a b : ℚ => b≤a) (List.ofFn x)).map (fun a : ℚ => (a : ℝ)) =
      List.insertionSort (fun a b : ℝ => b≤a) (List.ofFn (fun i => (x i : ℝ))) := by
    rw [List.map_insertionSort (r := fun a b : ℚ => b≤a) (s := fun a b : ℝ => b≤a)
      _ _ (fun a _ b _ => Rat.cast_le.symm)]
    simp only [List.map_ofFn,Function.comp_def]
  have hq : k.val<(List.insertionSort (fun a b : ℚ => b≤a) (List.ofFn x)).length := by simp
  have hr : k.val<(List.insertionSort (fun a b : ℝ => b≤a) (List.ofFn fun i => (x i : ℝ))).length := by simp
  have h := congrArg (fun l : List ℝ => l[k.val]?) hsort
  rw [countedOrderStatistic_sorted,countedOrderStatistic_sorted]
  simpa only [List.get_eq_getElem,List.getElem?_map,List.getElem?_eq_getElem hq,List.getElem?_eq_getElem hr,
    Option.map_some,Option.some.injEq] using h.symm

theorem countedPilot_ratCast (hm : 1≤m) (t : ℚ × ℚ) (a : Fin (outerPilotRounds m) → Fin n → ℚ × ℚ) :
    (countedPilot hm (castOuterPair t) (fun r i => castOuterPair (a r i))).1 =
      ((countedPilot hm t a).1 : ℝ) := by
  unfold countedPilot
  dsimp only
  simp_rw [countedRetainedMaximum_ratCast]
  exact countedOrderStatistic_ratCast _ _

lemma countedMeshIndex_ratCast (H y : ℚ) (k : ℕ) :
    countedMeshIndex (H : ℝ) (y : ℝ) k = countedMeshIndex H y k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [countedMeshIndex,countedMeshIndex]
    have h : (↑(k+1 : ℕ) : ℝ)*(H : ℝ)≤(y : ℝ) ↔ (↑(k+1 : ℕ) : ℚ)*H≤y := by
      rw [← Rat.cast_natCast,← Rat.cast_mul,Rat.cast_le]
    by_cases hp : (↑(k+1 : ℕ) : ℚ)*H≤y
    · rw [if_pos (h.mpr hp),if_pos hp]
    · rw [if_neg (mt h.mp hp),if_neg hp,ih]

lemma countedMeshRound_ratCast (H x : ℚ) (m : ℕ) :
    (countedMeshRound (H : ℝ) m (x : ℝ)).1=((countedMeshRound H m x).1 : ℝ) := by
  unfold countedMeshRound
  have hc : (H : ℝ)≤(x : ℝ) ↔ H≤x := Rat.cast_le
  have hx : (x : ℝ)≤0 ↔ x≤0 := by norm_cast
  by_cases hp : H≤x
  · rw [if_pos (hc.mpr hp),if_pos hp]
  · rw [if_neg (mt hc.mp hp),if_neg hp]
    by_cases h0 : x≤0
    · rw [if_pos (hx.mpr h0),if_pos h0]
      exact Rat.cast_zero.symm
    · rw [if_neg (mt hx.mp h0),if_neg h0]
      dsimp only
      rw [← Rat.cast_natCast,← Rat.cast_mul,countedMeshIndex_ratCast]
      push_cast
      rfl

theorem countedDisplay_ratCast (m : ℕ) (H : ℚ) (t z : ℚ × ℚ) :
    (countedDisplay m (H : ℝ) (castOuterPair t) (castOuterPair z)).1 =
      ((countedDisplay m H t z).1 : ℝ) := by
  unfold countedDisplay
  dsimp only
  rw [countedRetention_ratCast]
  have h : min (max (0 : ℝ) ((countedRetention t z : ℚ) / (H : ℝ))) 1 =
      ((min (max (0 : ℚ) (countedRetention t z/H)) 1 : ℚ) : ℝ) := by
    simp only [Rat.cast_min,Rat.cast_max,Rat.cast_zero,Rat.cast_one,Rat.cast_div]
  rw [h]
  simpa only [Rat.cast_one] using
    countedMeshRound_ratCast 1 (min (max (0 : ℚ) (countedRetention t z/H)) 1) m

theorem countedOuterPrepare_ratCast (hm : 1≤m) (cut : Fin m → Fin n → ℚ × ℚ)
    (pilot : Fin (outerPilotRounds m) → Fin n → ℚ × ℚ) (inner : Fin (2*m) → Fin n → ℚ × ℚ) :
    let q := countedOuterPrepare hm cut pilot inner
    let Q := countedOuterPrepare hm (fun r i => castOuterPair (cut r i))
      (fun r i => castOuterPair (pilot r i)) (fun r i => castOuterPair (inner r i))
    Q.cutoff=castOuterPair q.cutoff ∧ Q.pilot=(q.pilot : ℝ) ∧
      Q.displayed=(fun i j => (q.displayed i j : ℝ)) := by
  unfold countedOuterPrepare
  dsimp only
  rw [countedCutoff_ratCast,countedPilot_ratCast]
  let t := (countedCutoff hm cut).1
  let p := (countedPilot hm t pilot).1
  have hP : (p : ℝ)=0 ↔ p=0 := by norm_cast
  change (if (p : ℝ)=0 then _ else _ : CountedOuterPreparation ℝ n m).cutoff = _ ∧ _ ∧ _
  by_cases hp : p=0
  · rw [if_pos (hP.mpr hp), if_pos hp]
    simp
  · rw [if_neg (mt hP.mp hp), if_neg hp]
    refine ⟨rfl,rfl,?_⟩
    funext i j
    have hget {A : Type} {N : ℕ} (f : Fin N → A) (k : Fin N) :
        (Vector.ofFn f).get k=f k := Vector.getElem_ofFn k.isLt
    simp only [hget]
    have h : (1000 : ℝ)*(p : ℝ)=((1000*p : ℚ) : ℝ) := by norm_cast
    rw [h]
    exact countedDisplay_ratCast _ _ _ _

end ProphetSecretary.Statistics.Calibration
