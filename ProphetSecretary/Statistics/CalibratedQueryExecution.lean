import ProphetSecretary.Statistics.CalibrationWorkScales
import ProphetSecretary.Statistics.ScalarPlannerWorkQuery
import ProphetSecretary.Analysis.MultilevelTapeLayout

/-!
# Executing a data-selected query from its finite seed bank

The stored probability scan and level search select a block. The counted
list evaluator then runs the same scalar query as the measurable estimator.
The supplied seed bank is indexed by the public maximum level.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Model ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m : ℕ} {K : Type} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

def calibrationStoredRows (y : Fin n → Fin m → K) : Vector (List K) n :=
  plannerStoredRows (fun i j => max 0 (min 1 (y i j)))

def countedCalibrationBankCall (y : Fin n → Fin m → K) (x : ScalarPlannerListState n K)
    (R : ℕ) (h p : K) (HL : ∃ j : ℕ, (1/4 : K)^j ≤
      scalarPlannerPrecisionRatio (storedScalarPlannerWeight (calibrationStoredRows y) x) h)
    (HC : ∃ j : ℕ, (1/4 : K)^j ≤ p)
    (s : MultilevelSeedBank (PlannerFieldSeed n K) (confidenceCopyCount p HC) R) :
    MedianCopiesResult K :=
  let rows := calibrationStoredRows y
  let prep := countedPlannerProbabilities rows
  let frame := countedScalarPlannerFrame (plannerProbabilityRead prep.1) x
  let level := countedScalarPlannerLevel frame.1.weight h HL
  let j : Fin (R+1) := ⟨min R level.1,Nat.lt_succ_of_le (min_le_left _ _)⟩
  let q := countedScalarPlannerQueryAtLevel rows x j.val p HC (s j)
  {q with work := q.work+prep.2+frame.2+level.2+6*n*(m+1)+5}

lemma countedCalibrationBankCall_value (y : Reservoir n m) (x : ScalarPlannerListState n ℝ)
    (hx : x.1.Nodup) (R : ℕ) (h p : ℝ)
    (HL : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio
      (storedScalarPlannerWeight (calibrationStoredRows y) x) h)
    (HC : ∃ j : ℕ, (1/4 : ℝ)^j ≤ p)
    (s : ScalarPlannerSeedBank n R (confidenceCopyCount p HC)) :
    (countedCalibrationBankCall y x R h p HL HC s).value =
      scalarPlannerBankQuery R h p HC y (scalarPlannerListInterpret x) s := by
  let q := scalarPlannerClampRows (k := fun _ => m) y
  let β := storedScalarPlannerWeight (calibrationStoredRows y) x
  let l := (countedScalarPlannerLevel β h HL).1
  let j : Fin (R+1) := ⟨min R l,Nat.lt_succ_of_le (min_le_left _ _)⟩
  change (countedScalarPlannerQueryAtLevel (plannerStoredRows q) x j.val p HC (s j)).value = _
  rw [countedScalarPlannerQueryAtLevel_value q x hx]
  have hβ : β=scalarPlannerWeight q (scalarPlannerListInterpret x).1 :=
    storedScalarPlannerWeight_value q x hx
  have hLevel : scalarPlannerLevel (scalarPlannerWeight q (scalarPlannerListInterpret x).1) h = l := by
    rw [← hβ,scalarPlannerLevel,dif_pos HL]
  have hj : boundedScalarPlannerLevel R h q (scalarPlannerListInterpret x).1 = j := by
    apply Fin.ext
    change min R (scalarPlannerLevel (scalarPlannerWeight q (scalarPlannerListInterpret x).1) h) = min R l
    rw [hLevel]
  unfold scalarPlannerBankQuery
  dsimp only
  rw [hj]

def calibrationBankCallBound (n m R C : ℕ) : ℕ :=
  46*(n+1)*(m+1)+80*(n+1) +
    C*(400*scalarPlannerPrimitiveBound n m*16^R+3)+10*(C+1)^2+3*R+31

theorem countedCalibrationBankCall_work (y : Fin n → Fin m → K) (x : ScalarPlannerListState n K)
    (hx : x.1.Nodup) (R : ℕ) (h p : K)
    (HL : ∃ j : ℕ, (1/4 : K)^j ≤ scalarPlannerPrecisionRatio
      (storedScalarPlannerWeight (calibrationStoredRows y) x) h)
    (HC : ∃ j : ℕ, (1/4 : K)^j ≤ p)
    (s : MultilevelSeedBank (PlannerFieldSeed n K) (confidenceCopyCount p HC) R)
    (hR : (countedScalarPlannerLevel (storedScalarPlannerWeight (calibrationStoredRows y) x) h HL).1≤R) :
    (countedCalibrationBankCall y x R h p HL HC s).work ≤
      calibrationBankCallBound n m R (confidenceCopyCount p HC) := by
  let rows := calibrationStoredRows y
  let prep := countedPlannerProbabilities rows
  let frame := countedScalarPlannerFrame (plannerProbabilityRead prep.1) x
  let lev := countedScalarPlannerLevel frame.1.weight h HL
  let j : Fin (R+1) := ⟨min R lev.1,Nat.lt_succ_of_le (min_le_left _ _)⟩
  let C := confidenceCopyCount p HC
  have hRows (i : Fin n) : (rows.get i).length≤m := by
    simp [rows,calibrationStoredRows]
  have hp := countedPlannerProbabilities_work rows m hRows
  have hf := countedScalarPlannerFrame_work (plannerProbabilityRead prep.1) x hx
  have hL := (countedScalarPlannerLevel_work frame.1.weight h HL).trans (show 3*lev.1+21≤3*R+21 by
    change lev.1≤R at hR
    omega)
  have hQ := countedScalarPlannerQueryAtLevel_work rows m hRows x hx j.val p HC (s j)
  have hQ' : (countedScalarPlannerQueryAtLevel rows x j.val p HC (s j)).work ≤
      20*(n+1)*(m+1)+40*(n+1)+C*(400*scalarPlannerPrimitiveBound n m*16^R+3)+10*(C+1)^2+5 := by
    have hPow : (16 : ℕ)^j.val≤16^R :=
      Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ j.isLt)
    have hW := Nat.mul_le_mul_left C (Nat.add_le_add_right
      (Nat.mul_le_mul_left (400*scalarPlannerPrimitiveBound n m) hPow) 3)
    exact hQ.trans (Nat.add_le_add_right
      (Nat.add_le_add_right (Nat.add_le_add_left hW _) _) _)
  have hClamp : 6*n*(m+1)≤6*(n+1)*(m+1) := by gcongr; omega
  change (countedScalarPlannerQueryAtLevel rows x j.val p HC (s j)).work +
    prep.2+frame.2+lev.2+6*n*(m+1)+5 ≤ _
  unfold calibrationBankCallBound
  change prep.2≤20*(n+1)*(m+1) at hp
  change frame.2≤40*(n+1) at hf
  change lev.2≤3*R+21 at hL
  change (countedScalarPlannerQueryAtLevel rows x j.val p HC (s j)).work +
    prep.2+frame.2+lev.2+6*n*(m+1)+5 ≤
    46*(n+1)*(m+1)+80*(n+1)+(C*(400*scalarPlannerPrimitiveBound n m*16^R+3))+
      10*(C+1)^2+3*R+31
  rw [show 46*(n+1)*(m+1) = 20*(n+1)*(m+1)+20*(n+1)*(m+1)+6*(n+1)*(m+1) by ring]
  omega

lemma countedCalibrationBankCall_level_le [NeZero m] (y : Reservoir n m)
    (x : ScalarPlannerListState n ℝ) (hx : x.1.Nodup) (h : ℝ) (hh : h∈Ioo (0 : ℝ) 1)
    (hCount : (totalEmpiricalInstance (scalarPlannerClampRows (k := fun _ => m) y)).positiveCount ≤ targetCountCutoff m)
    (HL : ∃ j : ℕ, (1/4 : ℝ)^j ≤ scalarPlannerPrecisionRatio
      (storedScalarPlannerWeight (calibrationStoredRows y) x) h) :
    (countedScalarPlannerLevel (storedScalarPlannerWeight (calibrationStoredRows y) x) h HL).1 ≤
      calibrationPlannerLevel m h := by
  let q := scalarPlannerClampRows (k := fun _ => m) y
  let A := (scalarPlannerListInterpret x).1
  let β := scalarPlannerWeight q A
  have hb : storedScalarPlannerWeight (calibrationStoredRows y) x = β :=
    storedScalarPlannerWeight_value q x hx
  have hβ := scalarPlannerWeight_ge_one q A
  have hB := scalarPlannerWeight_le_calibrationBound q (fun i j => le_max_left _ _) hCount A
  have hErr := calibrationPlannerLevel_error (zero_le_one.trans hβ) hB hh
  have hLevel : scalarPlannerLevel β h =
      (countedScalarPlannerLevel (storedScalarPlannerWeight (calibrationStoredRows y) x) h HL).1 := by
    rw [← hb,scalarPlannerLevel,dif_pos HL]
  rw [← hLevel]
  exact scalarPlannerLevel_le_of_error hβ hh hErr

/-- Clamping a raw bounded-learner row does not change which samples are
positive. The count guard therefore bounds query work even on raw inputs. -/
lemma calibrationClamped_positiveCount [NeZero m] (y : Reservoir n m) :
    (totalEmpiricalInstance (scalarPlannerClampRows (k := fun _ => m) y)).positiveCount =
      (totalEmpiricalInstance y).positiveCount := by
  have h0 (i : Fin n) (j : Fin m) : 0 ≤ scalarPlannerClampRows (k := fun _ => m) y i j :=
    le_max_left _ _
  let a := scalarPlannerClampRows (k := fun _ => m) y
  let b := nonnegativeReservoir y
  have ha : (totalEmpiricalInstance a).positiveCount =
      ∑ i : Fin n, plannerPositiveProbability (k := fun _ => m) a i := by
    rw [← planner_empirical_eq a h0]
    change (∑ i : Fin n, (empiricalLaw (a i)).real (Ioi 0)) = _
    apply Finset.sum_congr rfl
    intro i _
    exact empiricalLaw_positiveProbability (a i)
  have hb : (totalEmpiricalInstance y).positiveCount =
      ∑ i : Fin n, plannerPositiveProbability (k := fun _ => m) b i := by
    change (∑ i : Fin n, (empiricalLaw (b i)).real (Ioi 0)) = _
    apply Finset.sum_congr rfl
    intro i _
    exact empiricalLaw_positiveProbability (b i)
  rw [ha,hb]
  apply Finset.sum_congr rfl
  intro i _
  unfold plannerPositiveProbability empiricalPositiveProbability
  apply congrArg (fun d : ℕ => (d : ℝ)/(m : ℝ))
  congr 1
  ext j
  simp only [positiveObservations,Finset.mem_filter,Finset.mem_univ,true_and,a,b,
    scalarPlannerClampRows,plannerUnit,nonnegativeReservoir,lt_sup_iff,lt_inf_iff,
    lt_self_iff_false,zero_lt_one,false_or,true_and]

def calibrationListState (A : Finset (Fin n)) (u z : ℝ) : ScalarPlannerListState n ℝ :=
  ((List.finRange n).filter (fun i => decide (i∈A)),u,z)

lemma calibrationListState_nodup (A : Finset (Fin n)) (u z : ℝ) :
    (calibrationListState A u z).1.Nodup :=
  (List.nodup_finRange n).filter _

lemma calibrationListState_interpret (A : Finset (Fin n)) (u z : ℝ) :
    scalarPlannerListInterpret (calibrationListState A u z)=(A,(u,z)) := by
  have h : ((List.finRange n).filter (fun i => decide (i∈A))).toFinset=A := by
    ext i
    simp
  simp only [scalarPlannerListInterpret,calibrationListState,h]

private lemma storedCalibrationWeight_ge_one (y : Reservoir n m) (A : Finset (Fin n)) (u z : ℝ) :
    1≤storedScalarPlannerWeight (calibrationStoredRows y) (calibrationListState A u z) := by
  change 1≤storedScalarPlannerWeight (plannerStoredRows (scalarPlannerClampRows (k := fun _ => m) y))
    (calibrationListState A u z)
  rw [storedScalarPlannerWeight_value _ _ (calibrationListState_nodup A u z)]
  exact scalarPlannerWeight_ge_one _ _

noncomputable def countedRealCalibrationCall (h p : ℝ) (hh : h∈Ioo (0 : ℝ) 1)
    (hp : p∈Ioo (0 : ℝ) 1) (y : Reservoir n m) (A : Finset (Fin n)) (u z : ℝ)
    (s : CalibrationPlannerSeed n m h p hp) : MedianCopiesResult ℝ :=
  let x := calibrationListState A u z
  let H := scalarPlannerPrecision_exists (storedCalibrationWeight_ge_one y A u z) hh
  let q := countedCalibrationBankCall y x (calibrationPlannerLevel m h) h p H
    (exists_confidence_level hp.1 hp.2) s
  {q with work := q.work+(n+1)^2+3}

lemma countedRealCalibrationCall_value (h p : ℝ) (hh : h∈Ioo (0 : ℝ) 1)
    (hp : p∈Ioo (0 : ℝ) 1) (y : Reservoir n m) (A : Finset (Fin n)) (u z : ℝ)
    (s : CalibrationPlannerSeed n m h p hp) :
    (countedRealCalibrationCall h p hh hp y A u z s).value=calibrationPlannerCall h p hp y A u z s := by
  unfold countedRealCalibrationCall calibrationPlannerCall
  dsimp only
  rw [countedCalibrationBankCall_value _ _ (calibrationListState_nodup A u z),
    calibrationListState_interpret]

lemma countedRealCalibrationCall_work [NeZero m] (h p : ℝ) (hh : h∈Ioo (0 : ℝ) 1)
    (hp : p∈Ioo (0 : ℝ) 1) (y : Reservoir n m)
    (hc : (totalEmpiricalInstance y).positiveCount≤targetCountCutoff m)
    (A : Finset (Fin n)) (u z : ℝ) (s : CalibrationPlannerSeed n m h p hp) :
    (countedRealCalibrationCall h p hh hp y A u z s).work ≤
      calibrationBankCallBound n m (calibrationPlannerLevel m h)
        (confidenceCopyCount p (exists_confidence_level hp.1 hp.2)) + (n+1)^2+3 := by
  let x := calibrationListState A u z
  let H := scalarPlannerPrecision_exists (storedCalibrationWeight_ge_one y A u z) hh
  have hc' : (totalEmpiricalInstance (scalarPlannerClampRows (k := fun _ => m) y)).positiveCount≤
      targetCountCutoff m := by rw [calibrationClamped_positiveCount]; exact hc
  have hR := countedCalibrationBankCall_level_le y x (calibrationListState_nodup A u z) h hh hc' H
  have hw := countedCalibrationBankCall_work y x (calibrationListState_nodup A u z)
    (calibrationPlannerLevel m h) h p H (exists_confidence_level hp.1 hp.2) s hR
  exact Nat.add_le_add_right (Nat.add_le_add_right hw ((n+1)^2)) 3

end ProphetSecretary.Statistics.Calibration
