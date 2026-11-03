import ProphetSecretary.Statistics.CalibratedQueryExecution
import ProphetSecretary.Statistics.CalibrationQueryTapes
import ProphetSecretary.Statistics.ScalarPlannerQueryRationalHeight
import ProphetSecretary.Statistics.CalibratedFairCalls

/-!
# The bounded rational fair-bank query

The level search stops at its public cap even on inputs outside the count
guard. Before the cap it chooses the least level meeting the squared-error
tolerance. Only the selected bank block is decoded for evaluation.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

def countedHalfPrecisionSearch (ρ a : ℚ) : ℕ → ℕ × ℕ
  | 0 => (0,1)
  | R+1 => if a≤ρ then (0,1) else
    let q := countedHalfPrecisionSearch ρ (a/2) R
    (q.1+1,q.2+3)

lemma countedHalfPrecisionSearch_spec (ρ a : ℚ) (R : ℕ) :
    let q := countedHalfPrecisionSearch ρ a R
    q.1 ≤ R ∧ q.2 ≤ 3*R+1 ∧
      (∀ j : ℕ, j<q.1 → ρ < a*(1/2:ℚ)^j) ∧
      (q.1<R → a*(1/2:ℚ)^q.1 ≤ ρ) := by
  induction R generalizing a with
  | zero => simp [countedHalfPrecisionSearch]
  | succ R ih =>
    by_cases h : a≤ρ
    · simp [countedHalfPrecisionSearch,h]
    · let q := countedHalfPrecisionSearch ρ (a/2) R
      have hq := ih (a/2)
      have he (j : ℕ) : a*(1/2:ℚ)^(j+1) = (a/2)*(1/2:ℚ)^j := by rw [pow_succ]; ring
      simp only [countedHalfPrecisionSearch,if_neg h]
      refine ⟨Nat.succ_le_succ hq.1,by have := hq.2.1; omega,?_,?_⟩
      · intro j hj
        cases j with
        | zero => simpa only [pow_zero,mul_one] using lt_of_not_ge h
        | succ j => rw [he]; exact hq.2.2.1 j (Nat.lt_of_succ_lt_succ hj)
      · intro hj
        rw [he]
        exact hq.2.2.2 (Nat.lt_of_succ_lt_succ hj)

lemma countedHalfPrecisionSearch_eq_min (ρ a : ℚ) (R r : ℕ)
    (hr : a*(1/2:ℚ)^r ≤ ρ) (hLeast : ∀ j<r, ρ < a*(1/2:ℚ)^j) :
    (countedHalfPrecisionSearch ρ a R).1 = min R r := by
  let q := countedHalfPrecisionSearch ρ a R
  have hq := countedHalfPrecisionSearch_spec ρ a R
  apply le_antisymm
  · exact le_min hq.1 (le_of_not_gt (fun h => (not_lt_of_ge hr) (hq.2.2.1 r h)))
  · by_cases h : q.1 < R
    · exact (min_le_right _ _).trans (le_of_not_gt (fun ht => (not_lt_of_ge (hq.2.2.2 h)) (hLeast q.1 ht)))
    · exact (min_le_left _ _).trans (le_of_not_gt h)

variable {n m : ℕ}

def countedRationalFairBankCall (y : Fin n → Fin m → ℚ) (x : ScalarPlannerListState n ℚ)
    (b R : ℕ) (h p : ℚ) (H : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p)
    (s : FairQueryBank n b (confidenceCopyCount p H) R) : MedianCopiesResult ℚ :=
  let rows := calibrationStoredRows y
  let prep := countedPlannerProbabilities rows
  let frame := countedScalarPlannerFrame (plannerProbabilityRead prep.1) x
  let r := countedHalfPrecisionSearch (scalarPlannerPrecisionRatio frame.1.weight (h/2)) 1 R
  let j : Fin (R+1) := ⟨r.1,Nat.lt_succ_of_le (countedHalfPrecisionSearch_spec _ _ R).1⟩
  let q := countedRationalFairQueryAtLevel rows x j.val p H b (s j)
  {q with work := q.work+prep.2+frame.2+r.2+6*n*(m+1)+15}

def rationalFairBankCallWorkBound (n m b R C : ℕ) : ℕ :=
  46*(n+1)*(m+1)+80*(n+1)+C*(400*scalarPlannerPrimitiveBound n m*16^R+3)+
    10*(C+1)^2+4*C*16^R*(plannerFairDecodeBound n b+40)+11*R+4*C+100

theorem countedRationalFairBankCall_work (y : Fin n → Fin m → ℚ) (x : ScalarPlannerListState n ℚ)
    (hx : x.1.Nodup) (b R : ℕ) (h p : ℚ) (H : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p)
    (s : FairQueryBank n b (confidenceCopyCount p H) R) :
    (countedRationalFairBankCall y x b R h p H s).work ≤
      rationalFairBankCallWorkBound n m b R (confidenceCopyCount p H) := by
  let rows := calibrationStoredRows y
  let prep := countedPlannerProbabilities rows
  let frame := countedScalarPlannerFrame (plannerProbabilityRead prep.1) x
  let ρ := scalarPlannerPrecisionRatio frame.1.weight (h/2)
  let r := countedHalfPrecisionSearch ρ 1 R
  let j : Fin (R+1) := ⟨r.1,Nat.lt_succ_of_le (countedHalfPrecisionSearch_spec _ _ R).1⟩
  let C := confidenceCopyCount p H
  have hRows (i : Fin n) : (rows.get i).length ≤ m := by simp [rows,calibrationStoredRows]
  have hP : prep.2 ≤ 20*(n+1)*(m+1) := countedPlannerProbabilities_work rows m hRows
  have hF : frame.2 ≤ 40*(n+1) := countedScalarPlannerFrame_work (plannerProbabilityRead prep.1) x hx
  have hR : j.val ≤ R := (countedHalfPrecisionSearch_spec ρ 1 R).1
  have hr : r.2 ≤ 3*R+1 := (countedHalfPrecisionSearch_spec ρ 1 R).2.1
  have hQ := countedRationalFairQueryAtLevel_work rows m hRows x hx j.val p H b (s j)
  have hPow := Nat.pow_le_pow_right (by decide : 0 < (16:ℕ)) hR
  have hV := Nat.mul_le_mul_left C (Nat.add_le_add_right (Nat.mul_le_mul_left (400*scalarPlannerPrimitiveBound n m) hPow) 3)
  have hD := Nat.mul_le_mul_right (plannerFairDecodeBound n b+40) (Nat.mul_le_mul_left (4*C) hPow)
  change (countedRationalFairQueryAtLevel rows x j.val p H b (s j)).work+prep.2+frame.2+r.2+6*n*(m+1)+15 ≤ _
  have hClamp := Nat.mul_le_mul_right (m+1) (Nat.mul_le_mul_left 6 (Nat.le_succ n))
  change 6*n*(m+1) ≤ 6*(n+1)*(m+1) at hClamp
  change (countedRationalFairQueryAtLevel rows x j.val p H b (s j)).work ≤
      20*(n+1)*(m+1)+40*(n+1)+C*(400*scalarPlannerPrimitiveBound n m*16^j.val+3)+10*(C+1)^2+45+
        4*C*16^j.val*(plannerFairDecodeBound n b+40)+8*j.val+4*C+21 at hQ
  change _ ≤ 46*(n+1)*(m+1)+80*(n+1)+C*(400*scalarPlannerPrimitiveBound n m*16^R+3)+
    10*(C+1)^2+4*C*16^R*(plannerFairDecodeBound n b+40)+11*R+4*C+100
  rw [show 46*(n+1)*(m+1)=20*(n+1)*(m+1)+20*(n+1)*(m+1)+6*(n+1)*(m+1) by ring]
  omega

/-- The bounded arithmetic search chooses the block used by the real
fair-bit query, with identical bits in every corresponding copy. -/
theorem countedRationalFairBankCall_value (y : Fin n → Fin m → ℚ) (x : ScalarPlannerListState n ℚ)
    (hx : x.1.Nodup) (b : ℕ) (h p : ℚ) (hh : (h:ℝ) ∈ Set.Ioo (0:ℝ) 1)
    (hp : (p:ℝ) ∈ Set.Ioo (0:ℝ) 1) (Hq : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p)
    (s : CalibrationFairSeed n m b (h:ℝ) (p:ℝ) hp) :
    let Hr := exists_confidence_level hp.1 hp.2
    let R := calibrationPlannerLevel m ((h:ℝ)/2)
    let bank : FairQueryBank n b (confidenceCopyCount p Hq) R :=
      fun j c => s j (Fin.cast (confidenceCopyCount_ratCast p Hq Hr).symm c)
    ((countedRationalFairBankCall y x b R h p Hq bank).value : ℝ) =
      calibrationFairCall b (h:ℝ) (p:ℝ) hp (fun i j => (y i j:ℝ)) x.1.toFinset (x.2.1:ℝ) (x.2.2:ℝ) s := by
  let Hr := exists_confidence_level hp.1 hp.2
  let R := calibrationPlannerLevel m ((h:ℝ)/2)
  let cEq := confidenceCopyCount_ratCast p Hq Hr
  let bank : FairQueryBank n b (confidenceCopyCount p Hq) R := fun j c => s j (Fin.cast cEq.symm c)
  let v := fun i j => max 0 (min 1 (y i j))
  let vR := fun i j => (v i j:ℝ)
  let A := x.1.toFinset
  let xR := scalarPlannerListInterpret (scalarPlannerStateRatCast x)
  let β := storedScalarPlannerWeight (plannerStoredRows v) x
  let βR := scalarPlannerWeight vR A
  let ρ := scalarPlannerPrecisionRatio β (h/2)
  let j : Fin (R+1) := ⟨(countedHalfPrecisionSearch ρ 1 R).1,
    Nat.lt_succ_of_le (countedHalfPrecisionSearch_spec _ _ R).1⟩
  have hβ : (β:ℝ)=βR := by
    change ((storedScalarPlannerWeight (plannerStoredRows v) x : ℚ):ℝ) = _
    rw [← storedScalarPlannerWeight_ratCast,plannerRowsRatCast_ofFn]
    exact storedScalarPlannerWeight_value vR (scalarPlannerStateRatCast x) hx
  have hv : vR = scalarPlannerClampRows (k := fun _ => m) (fun i j => (y i j:ℝ)) := by
    funext i l
    simp [vR,v,scalarPlannerClampRows,plannerUnit,Rat.cast_max,Rat.cast_min]
  have hb : 1 ≤ βR := scalarPlannerWeight_ge_one vR A
  have hh' : (h:ℝ)/2 ∈ Set.Ioo (0:ℝ) 1 := ⟨by linarith [hh.1],by linarith [hh.2]⟩
  let H := scalarPlannerPrecision_exists hb hh'
  let l := (countedScalarPlannerLevel βR ((h:ℝ)/2) H).1
  have hρ : (ρ:ℝ) = scalarPlannerPrecisionRatio βR ((h:ℝ)/2) := calc
    _ = scalarPlannerPrecisionRatio (β:ℝ) ((h/2:ℚ):ℝ) := (scalarPlannerPrecisionRatio_ratCast β (h/2)).symm
    _ = _ := by simp [hβ]
  have hCast (k : ℕ) : (((1/2:ℚ)^k : ℚ):ℝ) = (1/2:ℝ)^k := by simp [Rat.cast_pow]
  have hOk : 1*(1/2:ℚ)^l ≤ ρ := by
    rw [one_mul,← Rat.cast_le (K := ℝ),hCast,hρ]
    exact countedScalarPlannerLevel_precision hb hh' H
  have hBefore (k : ℕ) (hk : k<l) : ρ < 1*(1/2:ℚ)^k := by
    rw [one_mul,← Rat.cast_lt (K := ℝ),hCast,hρ]
    exact countedScalarPlannerLevel_least hb hh' H k hk
  have hj : j = boundedScalarPlannerLevel R ((h:ℝ)/2) vR A := by
    apply Fin.ext
    change (countedHalfPrecisionSearch ρ 1 R).1 = min R (scalarPlannerLevel βR ((h:ℝ)/2))
    rw [scalarPlannerLevel,dif_pos H]
    exact countedHalfPrecisionSearch_eq_min ρ 1 R l hOk hBefore
  change ((countedRationalFairQueryAtLevel (plannerStoredRows v) x j.val p Hq b (bank j)).value:ℝ) = _
  rw [countedRationalFairQueryAtLevel_value v x hx j.val p Hq Hr b (bank j)]
  have hBank : (fun i => bank j (Fin.cast cEq i)) = s j := by
    funext i
    simp [bank]
  change (scalarPlannerFairQuery vR b xR j.val (p:ℝ) Hr (fun i => bank j (Fin.cast cEq i))).value = _
  rw [hBank,hj]
  unfold calibrationFairCall calibrationPlannerCall scalarPlannerBankQuery
  dsimp only
  rw [← hv]
  rfl

def finiteFairBankOutputHeight (n m Y M U Z b R : ℕ) : ℕ :=
  n*(2*M+3)+64*(plannerPrimitiveHeight n m Y M (2*M) U Z b R+R+1)*16^R+3

theorem countedRationalFairBankCall_height (y : Fin n → Fin m → ℚ) (x : ScalarPlannerListState n ℚ)
    (hx : x.1.Nodup) (b R : ℕ) (h p : ℚ) (H : ∃ j : ℕ, (1/4 : ℚ)^j ≤ p)
    (s : FairQueryBank n b (confidenceCopyCount p H) R) (Y M U Z : ℕ)
    (hm : m≤2^M) (hy : ∀ i j, RationalHeight (y i j) Y)
    (hU : RationalHeight x.2.1 U) (hZ : RationalHeight x.2.2 Z) (hz : 2≤Z) :
    RationalHeight (countedRationalFairBankCall y x b R h p H s).value
      (finiteFairBankOutputHeight n m Y M U Z b R) := by
  let rows := calibrationStoredRows y
  let prep := countedPlannerProbabilities rows
  let frame := countedScalarPlannerFrame (plannerProbabilityRead prep.1) x
  let ρ := scalarPlannerPrecisionRatio frame.1.weight (h/2)
  let r := countedHalfPrecisionSearch ρ 1 R
  let j : Fin (R+1) := ⟨r.1,Nat.lt_succ_of_le (countedHalfPrecisionSearch_spec _ _ R).1⟩
  have hRows (i : Fin n) : (rows.get i).length≤m := by simp [rows,calibrationStoredRows]
  have hData (i : Fin n) (a : ℚ) (ha : a∈rows.get i) : RationalHeight a Y := by
    simp only [rows,calibrationStoredRows,plannerStoredRows_get] at ha
    obtain ⟨k,rfl⟩ := List.mem_ofFn.mp ha
    exact rationalHeight_unitClamp (hy i k)
  have hR : j.val≤R := (countedHalfPrecisionSearch_spec ρ 1 R).1
  have hq := countedRationalFairQueryAtLevel_height rows m Y M U Z b j.val hRows hm hData hz x hx hU hZ p H (s j)
  change RationalHeight (countedRationalFairQueryAtLevel rows x j.val p H b (s j)).value _
  apply hq.mono
  have hH := Nat.mul_le_mul_right b hR
  have hb : plannerPrimitiveHeight n m Y M (2*M) U Z b j.val+j.val+1 ≤
      plannerPrimitiveHeight n m Y M (2*M) U Z b R+R+1 := by
    unfold plannerPrimitiveHeight
    omega
  unfold finiteFairBankOutputHeight
  exact Nat.add_le_add_right (Nat.add_le_add_left
    (Nat.mul_le_mul (Nat.mul_le_mul_left 64 hb) (Nat.pow_le_pow_right (by decide) hR)) _) 3

end ProphetSecretary.Statistics.Calibration
