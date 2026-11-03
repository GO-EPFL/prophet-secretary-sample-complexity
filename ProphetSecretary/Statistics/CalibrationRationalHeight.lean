import ProphetSecretary.Statistics.CountedCalibrationPrepare
import ProphetSecretary.Statistics.CalibrationInterpolation
import ProphetSecretary.Statistics.EmpiricalMaximumHeight

/-!
# Rational operands in the finite calibration

Validation records either a supplied timestamp or one. Each knot is a finite
average. Calibration scans these fixed knots and divides once to obtain a
mixing fraction on the selected segment.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis

variable {n m J : ℕ} {TSeed PSeed : Type}

lemma rankMemoThreshold_operands_height (z s cached : ℚ) (Z B E : ℕ)
    (hz : RationalHeight z Z) (hs : RationalHeight s B) (hc : RationalHeight cached E) :
    let u := max 0 (min 1 (1-s))
    RationalHeight u (B+1) ∧ RationalHeight (z*u) (Z+B+1) ∧
      RationalHeight (max (z*u) cached) (max (Z+B+1) E) := by
  have h₀ := rationalHeight_one.sub hs
  have hu : RationalHeight (max 0 (min 1 (1-s))) (B+1) :=
    (rationalHeight_zero.max (rationalHeight_one.min h₀)).mono (by simp)
  have hZ := (hz.mul hu).mono (by omega : Z+(B+1) ≤ Z+B+1)
  exact ⟨hu,hZ,hZ.max hc⟩

private lemma scanlMax_height (l : List ℚ) (a : ℚ) (B : ℕ)
    (ha : RationalHeight a B) (hl : ∀ x ∈ l, RationalHeight x B) (x : ℚ) (hx : x ∈ l.scanl max a) :
    RationalHeight x B := by
  induction l generalizing a with
  | nil =>
    simp only [List.scanl_nil,List.mem_singleton] at hx
    rwa [hx]
  | cons y l ih =>
    rw [List.scanl_cons,List.mem_cons] at hx
    rcases hx with h | h
    · rwa [h]
    · exact ih (max a y) ((ha.max (hl y List.mem_cons_self)).mono (max_le le_rfl le_rfl))
        (fun z hz => hl z (List.mem_cons_of_mem _ hz)) h

lemma countedRankPrefixRow_height (z : ℕ → ℚ)
    (estimate : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ × ℕ) (q : Fin n → Fin m → ℚ)
    (p : Equiv.Perm (Fin n)) (s : Fin n → ℚ) (r : PolicyQueryArray n J PSeed)
    (k : Fin n) (j E : ℕ) (hE : ∀ l : ℕ, l ≤ J →
      RationalHeight (estimate (rankContinuationSet q p k) (max 0 (min 1 (1-s k)))
        (z l) (r (k,coefficientIndex J l))).1 E) :
    RationalHeight (((countedRankPrefixRow z estimate q p s r k).1[j]?).getD 0) E := by
  let A := rankContinuationSet q p k
  let u := max 0 (min 1 (1-s k))
  let call := fun l : ℕ => estimate A u (z l) (r (k,coefficientIndex J l))
  let l := (List.ofFn (fun i : Fin J => call (i.val+1))).map Prod.fst
  let a := (call 0).1
  change RationalHeight ((l.scanl max a).toArray[j]?.getD 0) E
  cases h : (l.scanl max a).toArray[j]? with
  | none => exact rationalHeight_zero.mono (Nat.zero_le _)
  | some x =>
    have hl : ∀ y ∈ l, RationalHeight y E := by
      intro y hy
      obtain ⟨v,hv,rfl⟩ := List.mem_map.mp hy
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
      exact hE (i.val+1) i.isLt
    exact scanlMax_height l a E (hE 0 (Nat.zero_le _)) hl x (by simpa using Array.mem_of_getElem? h)

lemma countedRankValidationMemo_duration_height (z : ℕ → ℚ)
    (estimate : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ × ℕ) (q : Fin n → Fin m → ℚ)
    (fallback : Bool) (p : Equiv.Perm (Fin n)) (x s : Fin n → ℚ)
    (r : PolicyQueryArray n J PSeed) (B k : ℕ) (hs : ∀ i, RationalHeight (s i) B) :
    RationalHeight (((countedRankValidationMemo z estimate q fallback p x s r).1[k]?).getD 1) B := by
  by_cases hk : k<J+1
  · simp only [countedRankValidationMemo,Array.getElem?_ofFn,hk,dite_true,Option.getD_some]
    let table := if fallback then #[] else Array.ofFn (countedRankPrefixRow z estimate q p s r)
    let found := (List.finRange n).find? (rankMemoAccepts z fallback (table.map Prod.fst) x s p ⟨k,hk⟩)
    change RationalHeight (found.elim 1 s) B
    cases found with
    | none => exact rationalHeight_one.mono (Nat.zero_le _)
    | some i => exact hs i
  · simp only [countedRankValidationMemo,Array.getElem?_ofFn,hk,dite_false,Option.getD_none]
    exact rationalHeight_one.mono (Nat.zero_le _)

lemma calibrationDurationAccumulator_height (duration : Fin m → Array ℚ) (k B : ℕ)
    (hD : ∀ (r : Fin m) (j : ℕ), RationalHeight (((duration r)[j]?).getD 1) B) (s : Finset (Fin m)) :
    RationalHeight (∑ r ∈ s, ((duration r)[k]?).getD 1) (m*(B+1)) := by
  have h := rationalHeight_sum s (fun r => ((duration r)[k]?).getD 1) (fun _ => B)
    (fun r _ => hD r k)
  have hc : s.card ≤ m := (Finset.card_le_univ s).trans_eq (Fintype.card_fin m)
  exact h.mono (by simpa only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] using Nat.mul_le_mul_right (B+1) hc)

lemma countedCalibrationKnots_height (duration : Fin m → Array ℚ) (J k B P : ℕ)
    (hm : m ≤ 2^P) (hD : ∀ (r : Fin m) (j : ℕ), RationalHeight (((duration r)[j]?).getD 1) B) :
    RationalHeight (((countedCalibrationKnots duration J)[k]?).getD 1) (m*(B+1)+P) := by
  by_cases hk : k<J+3
  · simp only [countedCalibrationKnots,Array.getElem?_ofFn,hk,dite_true,Option.getD_some]
    split_ifs
    · exact rationalHeight_zero.mono (Nat.zero_le _)
    · have hSum := calibrationDurationAccumulator_height duration (k-1) B hD Finset.univ
      exact ((rationalHeight_natCast m P hm).inv.mul hSum).mono (by omega)
    · exact rationalHeight_one.mono (Nat.zero_le _)
  · simp only [countedCalibrationKnots,Array.getElem?_ofFn,hk,dite_false,Option.getD_none]
    exact rationalHeight_one.mono (Nat.zero_le _)

lemma calibrationInterpolation_operands_height (v : ℕ → ℚ) (ρ : ℚ) (k B R : ℕ)
    (hv : ∀ j, RationalHeight (v j) B) (hρ : RationalHeight ρ R) :
    RationalHeight (ρ-v (k-1)) (R+B+1) ∧ RationalHeight (v k-v (k-1)) (2*B+1) ∧
      RationalHeight ((ρ-v (k-1))/(v k-v (k-1))) (R+3*B+2) := by
  have hN := hρ.sub (hv (k-1))
  have hD := (hv k).sub (hv (k-1))
  exact ⟨hN,hD.mono (by omega),(hN.div hD).mono (by omega)⟩

lemma calibrationMixingFraction_height (v : ℕ → ℚ) (ρ : ℚ) (N B R : ℕ)
    (hv : ∀ j, RationalHeight (v j) B) (hρ : RationalHeight ρ R) :
    RationalHeight (calibrationMixingFraction v ρ N) (R+3*B+2) :=
  (calibrationInterpolation_operands_height v ρ (calibrationCrossing v ρ N) B R hv hρ).2.2

lemma familyCoefficient_arithmetic_height (zlo zhi : ℚ) (J k B P : ℕ)
    (hJ : J ≤ 2^P) (hlo : RationalHeight zlo B) (hhi : RationalHeight zhi B) :
    RationalHeight (zlo+((min k J : ℕ):ℚ)/(J:ℚ)*(zhi-zlo)) (3*B+2*P+2) := by
  have h := (rationalHeight_natCast (min k J) P ((min_le_right _ _).trans hJ)).div
    (rationalHeight_natCast J P hJ)
  exact (hlo.add (h.mul (hhi.sub hlo))).mono (by omega)

lemma storedCalibrationCoefficient_height (J k B P : ℕ) (zlo zhi : ℚ)
    (hJ : J ≤ 2^P) (hlo : RationalHeight zlo B) (hhi : RationalHeight zhi B) :
    RationalHeight (storedCalibrationCoefficient J zlo zhi k) (3*B+2*P+2) := by
  simpa [storedCalibrationCoefficient,Vector.get,coefficientIndex] using
    familyCoefficient_arithmetic_height zlo zhi J k B P hJ hlo hhi

lemma calibrationGridScan_operands_height (m B P : ℕ) (zlo zhi : ℚ)
    (hm : m ≤ 2^P) (hlo : RationalHeight zlo B) (hhi : RationalHeight zhi B) :
    RationalHeight ((m:ℚ)*(zhi-zlo)) (P+2*B+1) ∧
      ∀ k : ℕ, k ≤ m → RationalHeight (k:ℚ) P :=
  ⟨((rationalHeight_natCast m P hm).mul (hhi.sub hlo)).mono (by omega),
    fun k hk => rationalHeight_natCast k P (hk.trans hm)⟩

lemma targetGridCoefficient_height (P : ℕ) (hm : m ≤ 2^P) (j : TargetGrid m) :
    RationalHeight ((j.val:ℚ)/(m:ℚ)) (2*P+2) := by
  have hJ : j.val ≤ 2^(P+2) := calc
    _ ≤ 4*m := Nat.le_of_lt_succ j.isLt
    _ ≤ 4*2^P := Nat.mul_le_mul_left _ hm
    _ = _ := by rw [pow_add]; ring
  exact ((rationalHeight_natCast j.val (P+2) hJ).div (rationalHeight_natCast m P hm)).mono (by omega)

lemma targetRatioCandidate_height (M : ℚ) (estimate : ℚ → TSeed → ℚ × ℕ) (P E B : ℕ)
    (hm : m ≤ 2^P) (hM : RationalHeight M B)
    (j : TargetGrid m) (r : TSeed) (hE : RationalHeight (estimate ((j.val:ℚ)/(m:ℚ)) r).1 E) :
    let z := (j.val:ℚ)/(m:ℚ)
    RationalHeight (((estimate z r).1+1/(m:ℚ))/(M+z)) (E+B+3*P+4) := by
  have hInv := rationalHeight_one.div (rationalHeight_natCast m P hm)
  have hZ := targetGridCoefficient_height P hm j
  exact ((hE.add hInv).div (hM.add hZ)).mono (by omega)

private lemma targetMinFold_height (l : List (ℚ × ℕ)) (a : ℚ × ℕ) (B : ℕ)
    (ha : RationalHeight a.1 B) (hl : ∀ x ∈ l, RationalHeight x.1 B) :
    RationalHeight (l.foldl (fun s q => (min s.1 q.1,s.2+q.2+2)) a).1 B := by
  induction l generalizing a with
  | nil => exact ha
  | cons x l ih =>
    exact ih _ ((ha.min (hl x List.mem_cons_self)).mono (max_le le_rfl le_rfl))
      (fun y hy => hl y (List.mem_cons_of_mem _ hy))

theorem countedTargetMinimum_height (mu L M Lbar : ℚ) (estimate : ℚ → TSeed → ℚ × ℕ)
    (r : TargetGrid m → TSeed) (P E B : ℕ) (hm : m ≤ 2^P) (hM : RationalHeight M B)
    (hE : ∀ j, RationalHeight (estimate ((j.val:ℚ)/(m:ℚ)) (r j)).1 E) :
    RationalHeight (countedTargetMinimum mu L M Lbar estimate r).1 (E+B+3*P+4) := by
  let C := E+B+3*P+4
  have h₄' : RationalHeight (4/5:ℚ) 3 := by
    simpa only [Int.cast_ofNat] using rationalHeight_of_fraction 4 5 (by decide) 3 (by decide) (by decide)
  have h₂' : RationalHeight (1/2:ℚ) 1 := by
    simpa only [Int.cast_one,Int.cast_ofNat] using rationalHeight_of_fraction 1 2 (by decide) 1 (by decide) (by decide)
  have h₄ : RationalHeight (4/5:ℚ) C := h₄'.mono (by dsimp [C]; omega)
  have h₂ : RationalHeight (1/2:ℚ) C := h₂'.mono (by dsimp [C]; omega)
  unfold countedTargetMinimum
  split_ifs
  · apply (h₂.max (targetMinFold_height _ (4/5,6) C h₄ ?_)).mono (max_le le_rfl le_rfl)
    intro a ha
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp ha
    exact targetRatioCandidate_height M estimate P E B hm hM j (r j) (hE j)
  · exact h₄

theorem countedKnotScan_interpolation_denominator_pos (v : ℕ → ℚ) (ρ : ℚ) (N : ℕ)
    (h0 : v 0 < ρ) (hN : ρ ≤ v N) :
    let k := (countedKnotScan v ρ 0 N).1
    0 < v k-v (k-1) := by
  rw [countedKnotScan_value,zero_add]
  simp only [zero_add]
  have h := calibrationCrossing_bounds v ρ N h0 hN
  exact sub_pos.mpr (h.2.2.1.trans_le h.2.2.2)

/-- The actual preparation performs one division on a selected pair of
stored knots. The size bound includes the empirical maximum and target
ratio computation, and uses only the recorded clock sizes for validation. -/
theorem countedCalibrationPrepare_mixing_height (mu zlo zhi Lbar : ℚ)
    (target : ℚ → TSeed → ℚ × ℕ)
    (estimate : Finset (Fin n) → ℚ → ℚ → PSeed → ℚ × ℕ)
    (q : Fin n → Fin m → ℚ) (r : TargetGrid m → TSeed)
    (profile : Fin m → CalibrationRankProfile n J ℚ PSeed)
    (P Y T B : ℕ) (hm : m ≤ 2^P) (hY : ∀ i j, RationalHeight (q i j) Y)
    (hT : ∀ j, RationalHeight (target ((j.val:ℚ)/(m:ℚ)) (r j)).1 T)
    (hB : ∀ r k, RationalHeight ((profile r).2.2.1 k) B) :
    let rows := empiricalStoredRows q
    let M := (rows.flatten.length+1)*(Y+4*P*rows.length+2)
    RationalHeight (countedCalibrationPrepare mu zlo zhi Lbar target estimate q r profile).selection.2
      (T+M+3*P+4+3*(m*(B+1)+P)+2) := by
  let rows := empiricalStoredRows q
  let H := (rows.flatten.length+1)*(Y+4*P*rows.length+2)
  let M := countedEmpiricalMaximum rows
  let p := countedPlannerProbabilities (plannerStoredRows q)
  let L := ∑ i : Fin n, plannerProbabilityRead p.1 i
  let fallback := decide (Lbar<L ∨ 1/4<M.1)
  let ρ := countedTargetMinimum mu L M.1 Lbar target r
  let z := storedCalibrationCoefficient J zlo zhi
  let vals : Vector (Array ℚ × ℕ) m := Vector.ofFn fun j =>
    let a := profile j
    countedRankValidationMemo z estimate q fallback a.1 a.2.1 a.2.2.1 a.2.2.2
  let d := fun j : Fin m => (vals.get j).1
  let A := countedCalibrationKnots d J
  let v := fun k : ℕ => (A[k]?).getD (1:ℚ)
  let k := (countedKnotScan v ρ.1 0 (J+2)).1
  have hL (row : List ℚ) (hr : row ∈ rows) : row.length ≤ 2^P := by
    change row ∈ List.ofFn (fun i => List.ofFn (q i)) at hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    simpa only [List.length_ofFn] using hm
  have hF (x : ℚ) (hx : x ∈ rows.flatten) : RationalHeight x Y := by
    obtain ⟨row,hr,hx'⟩ := List.mem_flatten.mp hx
    change row ∈ List.ofFn (fun i => List.ofFn (q i)) at hr
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hx'
    exact hY i j
  have hM : RationalHeight M.1 H := countedEmpiricalMaximum_height rows P Y hL hF
  have hρ := countedTargetMinimum_height mu L M.1 Lbar target r P T H hm hM hT
  have hD (j : Fin m) (k' : ℕ) : RationalHeight (((d j)[k']?).getD 1) B := by
    simpa [d,vals,Vector.get] using
      countedRankValidationMemo_duration_height z estimate q fallback (profile j).1
        (profile j).2.1 (profile j).2.2.1 (profile j).2.2.2 B k' (hB j)
  have hv (k' : ℕ) : RationalHeight (v k') (m*(B+1)+P) := countedCalibrationKnots_height d J k' B P hm hD
  exact (calibrationInterpolation_operands_height v ρ.1 k _ _ hv hρ).2.2

end ProphetSecretary.Statistics.Calibration
