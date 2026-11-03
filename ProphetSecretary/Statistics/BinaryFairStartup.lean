import ProphetSecretary.Statistics.BinaryPublicSearch
import ProphetSecretary.Statistics.BinaryCalibrationQueryInputs

/-!
# Binary startup for the fair scalar queries

The encoded inputs determine three positive thresholds: the half-power
stochastic tolerance, the grid tolerance, and the confidence tolerance.
The public searches compute their least levels before any query uses its
random tape.
-/

open Set

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

def binaryPlannerGridToleranceExpr (n beta h : BinaryRational) : CalibrationBinaryExpr :=
  .node .div (.node .mul (.atom (BinaryRational.ofRat 3)) (.atom h))
    (.node .mul (.node .mul (.atom (BinaryRational.ofRat 4)) (.atom beta))
      (.node .add (.node .mul (.atom (BinaryRational.ofRat 10)) (.atom n))
        (.atom (BinaryRational.ofRat 4))))

lemma binaryPlannerGridToleranceExpr_value (n : ℕ) (beta h : BinaryRational) :
    (binaryPlannerGridToleranceExpr (countedCalibrationNat n).1 beta h).value =
      plannerGridTolerance n beta.value h.value := by
  simp only [binaryPlannerGridToleranceExpr,CalibrationBinaryExpr.value,rationalCalibrationOp,
    BinaryRational.ofRat_value,countedCalibrationNat_value,plannerGridTolerance]

def countedBinaryFairStartup (n : ℕ) (beta h p : BinaryRational) : BinaryPublicSearchResult :=
  let N := countedCalibrationNat n
  let d := (binaryPlannerGridToleranceExpr N.1 beta h).evaluate
  let r := countedBinaryPrecisionRatio beta h
  let q := countedBinaryPublicSearch r.1 d.1 p
  {q with work := q.work+N.2+d.2+r.2+8}

private lemma countedConfidenceLevel_congr {p q : ℚ} (e : p=q)
    (P : ∃ j : ℕ, (1/4 : ℚ)^j≤p) (Q : ∃ j : ℕ, (1/4 : ℚ)^j≤q) :
    (countedConfidenceLevel p P).1=(countedConfidenceLevel q Q).1 := by
  subst q
  rfl

set_option maxHeartbeats 140000 in
theorem countedBinaryFairStartup_value (n m : ℕ) [NeZero m]
    (beta h p : BinaryRational) (hB : beta.value=rationalCalibrationWeightBound m)
    (hh : (h.value : ℝ)∈Ioo (0 : ℝ) 1) (hp : (p.value : ℝ)∈Ioo (0 : ℝ) 1) :
    let q := countedBinaryFairStartup n beta h p
    let s := nativePublicFairSchedule n m h.value p.value hh hp
    q.level=s.level ∧ q.precision=s.bits ∧ q.halfCopies=(countedConfidenceLevel s.failure s.confidence).1 := by
  let δ := (binaryPlannerGridToleranceExpr (countedCalibrationNat n).1 beta h).evaluate.1
  let ρ := (countedBinaryPrecisionRatio beta h).1
  let B := calibrationWeightBound m
  let d := plannerGridTolerance n B (h.value : ℝ)
  let r := scalarPlannerPrecisionRatio B ((h.value : ℝ)/2)
  have hβ : (beta.value : ℝ)=B := by rw [hB,rationalCalibrationWeightBound_cast]
  have hB1 : 1≤B := calibrationWeightBound_ge_one
  have hHalf : (h.value : ℝ)/2∈Ioo (0 : ℝ) 1 := ⟨by linarith [hh.1],by linarith [hh.2]⟩
  have hδQ : δ.value=plannerGridTolerance n (rationalCalibrationWeightBound m) h.value := by
    dsimp only [δ]
    rw [CalibrationBinaryExpr.evaluate_value,binaryPlannerGridToleranceExpr_value,hB]
  have hδ : (δ.value : ℝ)=d := by
    rw [hδQ]
    simp only [plannerGridTolerance,Rat.cast_mul,Rat.cast_div,Rat.cast_add,Rat.cast_ofNat,Rat.cast_natCast,
      rationalCalibrationWeightBound_cast,d,B]
  have hρ : (ρ.value : ℝ)=r := by
    dsimp only [ρ]
    rw [countedBinaryPrecisionRatio_value,← scalarPlannerPrecisionRatio_ratCast,hβ]
    simp only [Rat.cast_div,Rat.cast_ofNat,r]
  have hd : 0<d := plannerGridTolerance_pos n (zero_lt_one.trans_le hB1) hh.1
  have hd1 : d<1 := plannerGridTolerance_lt_one n hB1 hh.2.le
  have hr : 0<r := (scalarPlannerPrecisionRatio_mem hB1 hHalf).1
  let Hd := exists_confidence_level hd hd1
  let Hδ := (exists_quarter_pow_le_ratCast δ.value).mp (by rw [hδ]; exact Hd)
  let Hp := (exists_quarter_pow_le_ratCast p.value).mp (exists_confidence_level hp.1 hp.2)
  have hSpec := countedBinaryPublicSearch_spec ρ δ p
    (by exact_mod_cast (hρ.symm ▸ hr)) (by exact_mod_cast (hδ.symm ▸ hd))
    (by exact_mod_cast hp.1) Hδ Hp
  dsimp only at hSpec ⊢
  let s := nativePublicFairSchedule n m h.value p.value hh hp
  let Hr := scalarPlannerPrecision_exists hB1 hHalf
  let k := (countedScalarPlannerLevel B ((h.value : ℝ)/2) Hr).1
  have hk : s.level=k := by
    rw [nativePublicFairSchedule_level,calibrationPlannerLevel,scalarPlannerLevel,dif_pos Hr]
  have hkGood : (1/2 : ℚ)^k≤ρ.value := by
    have h := countedScalarPlannerLevel_precision hB1 hHalf Hr
    change (1/2 : ℝ)^k≤r at h
    rw [← hρ] at h
    apply (Rat.cast_le (K := ℝ)).mp
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have hkLeast (j : ℕ) (hj : j<k) : ρ.value<(1/2 : ℚ)^j := by
    have h := countedScalarPlannerLevel_least hB1 hHalf Hr j hj
    change r<(1/2 : ℝ)^j at h
    rw [← hρ] at h
    apply (Rat.cast_lt (K := ℝ)).mp
    simpa only [Rat.cast_pow,Rat.cast_div,Rat.cast_one,Rat.cast_ofNat] using h
  have hLevel : (countedBinaryPublicSearch ρ δ p).level=k := by
    apply le_antisymm
    · exact le_of_not_gt (fun h => (not_lt_of_ge hkGood) (hSpec.2.1 k h))
    · exact le_of_not_gt (fun h => (not_lt_of_ge hSpec.1) (hkLeast _ h))
  let Hnative : ∃ j : ℕ, (1/4 : ℚ)^j≤plannerGridTolerance n (rationalCalibrationWeightBound m) h.value :=
    hδQ ▸ Hδ
  have hNativeBits : s.bits=2*(countedConfidenceLevel
      (plannerGridTolerance n (rationalCalibrationWeightBound m) h.value) Hnative).1+1 := rfl
  have hBits : (countedBinaryPublicSearch ρ δ p).precision=s.bits := by
    exact hSpec.2.2.1.trans ((congrArg (fun j : ℕ => 2*j+1)
      (countedConfidenceLevel_congr hδQ Hδ Hnative)).trans hNativeBits.symm)
  have hf : s.failure=p.value := rfl
  have hC := countedConfidenceLevel_congr hf s.confidence Hp
  have hCopies : (countedBinaryPublicSearch ρ δ p).halfCopies=(countedConfidenceLevel s.failure s.confidence).1 :=
    hSpec.2.2.2.trans hC.symm
  unfold countedBinaryFairStartup
  dsimp only
  exact ⟨hLevel.trans hk.symm,hBits,hCopies⟩

def binaryFairStartupWorkBound (B : ℕ) : ℕ :=
  3*(B+1)+3+20*CalibrationBinaryExpr.workUnit 20 B+
    5*(3600*(4*B+15)^3)+8+binaryPublicSearchWorkBound (20*(B+1))+8

theorem countedBinaryFairStartup_work (n : ℕ) (beta h p : BinaryRational) (B : ℕ)
    (hB : 4≤B) (hn : n≤2^B)
    (hβ : RationalHeight beta.value B) (hh : RationalHeight h.value B)
    (hp : RationalHeight p.value B) :
    (countedBinaryFairStartup n beta h p).work≤binaryFairStartupWorkBound B := by
  let N := countedCalibrationNat n
  let e := binaryPlannerGridToleranceExpr N.1 beta h
  let d := e.evaluate
  let r := countedBinaryPrecisionRatio beta h
  have hN : RationalHeight N.1.value B := by
    rw [countedCalibrationNat_value]
    exact rationalHeight_natCast n B hn
  have h3 : RationalHeight (BinaryRational.ofRat 3).value B := by
    rw [BinaryRational.ofRat_value]
    exact (rationalHeight_natCast 3 2 (by decide)).mono (by omega)
  have h4 : RationalHeight (BinaryRational.ofRat 4).value B := by
    rw [BinaryRational.ofRat_value]
    exact (rationalHeight_natCast 4 2 (by decide)).mono (by omega)
  have h10 : RationalHeight (BinaryRational.ofRat 10).value B := by
    rw [BinaryRational.ofRat_value]
    exact (rationalHeight_natCast 10 4 (by decide)).mono hB
  have he : e.leavesFit B := ⟨⟨h3,hh⟩,⟨⟨h4,hβ⟩,⟨⟨h10,hN⟩,h4⟩⟩⟩
  have hs : e.size≤20 := by norm_num [e,binaryPlannerGridToleranceExpr,CalibrationBinaryExpr.size]
  have hd : RationalHeight d.1.value (20*(B+1)) := by
    dsimp only [d]
    rw [CalibrationBinaryExpr.evaluate_value]
    exact (e.value_height B he).mono (Nat.mul_le_mul_right _ hs)
  have hr : RationalHeight r.1.value (20*(B+1)) :=
    (countedBinaryPrecisionRatio_height beta h B B hβ hh).mono (by omega)
  have hSearch := countedBinaryPublicSearch_work r.1 d.1 p (20*(B+1)) hr hd (hp.mono (by omega))
  have hNW := countedCalibrationNat_work n B hn
  have hD := (e.evaluate_work 20 B he hs).trans
    (Nat.mul_le_mul_right (CalibrationBinaryExpr.workUnit 20 B) hs)
  have hR := countedBinaryPrecisionRatio_work beta h B B hβ hh
  have hEq : 2*B+2*B+15=4*B+15 := by omega
  rw [hEq] at hR
  change (countedBinaryPublicSearch r.1 d.1 p).work+N.2+d.2+r.2+8≤_
  unfold binaryFairStartupWorkBound
  change N.2≤3*(B+1)+3 at hNW
  change d.2≤20*CalibrationBinaryExpr.workUnit 20 B at hD
  change r.2≤5*(3600*(4*B+15)^3)+8 at hR
  omega

end ProphetSecretary.Statistics.Calibration
