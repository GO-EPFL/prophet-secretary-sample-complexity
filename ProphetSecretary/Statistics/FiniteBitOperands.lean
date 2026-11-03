import ProphetSecretary.Statistics.FiniteBitWork

/-!
# Boundary operand heights of the finite schedule

The displayed rows have the mesh denominator, the validation clocks have
the dyadic denominator, and the only integer floor acts on the scaled
mixing fraction computed from the selected knots.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

lemma countedRationalRankClocks_height {n : ℕ} (b : ℕ) (bits : RankCalibrationClockBits n b) (i : Fin n) :
    RationalHeight ((countedRationalRankClocks b bits).1.get i) b := by
  rw [show (countedRationalRankClocks b bits).1.get i = (countedDyadicSortedClocks b bits).1 i from
    congrFun (countedRationalRankClocks_value b bits) i]
  exact gridPoint_height b _

lemma countedStoredDyadicUniform_height (b : ℕ) (bits : Fin b → Bool) :
    RationalHeight (countedStoredDyadicUniform b bits).1 b := by
  rw [countedStoredDyadicUniform_value]
  exact gridPoint_height b _

lemma countedFiniteTargetCall_height {n m : ℕ} (T : FairCallSchedule) (y : Fin n → Fin m → ℚ)
    (z : ℚ) (s : T.Seed n) (Y M Z : ℕ) (hm : m≤2^M) (hy : ∀ i j, RationalHeight (y i j) Y)
    (hz : RationalHeight z Z) (hZ : 2≤Z) :
    RationalHeight (countedFiniteTargetCall T y z s).1
      (finiteFairBankOutputHeight n m Y M 0 Z T.bits T.level) :=
  countedRationalFairBankCall_height y (List.finRange n,1,z) (List.nodup_finRange n)
    T.bits T.level T.accuracy T.failure T.confidence s Y M 0 Z hm hy rationalHeight_one hz hZ

lemma countedFiniteThresholdCall_height {n m : ℕ} (P : FairCallSchedule) (y : Fin n → Fin m → ℚ)
    (A : Finset (Fin n)) (u z : ℚ) (s : P.Seed n) (Y M U Z : ℕ)
    (hm : m≤2^M) (hy : ∀ i j, RationalHeight (y i j) Y)
    (hu : RationalHeight u U) (hz : RationalHeight z Z) (hZ : 2≤Z) :
    RationalHeight (countedFiniteThresholdCall P y A u z s).1
      (finiteFairBankOutputHeight n m Y M U Z P.bits P.level) := by
  let l := countedPredicateFilter (fun i => i∈A) (List.finRange n)
  have h : l.1.Nodup := by rw [countedPredicateFilter_value]; exact (List.nodup_finRange n).filter _
  exact countedRationalFairBankCall_height y (l.1,u,z) h P.bits P.level P.accuracy P.failure P.confidence
    s Y M U Z hm hy hu hz hZ

lemma countedDisplay_height {m : ℕ} (H : ℚ) (t x : ℚ × ℚ) (M : ℕ) (hm : m≤2^M) :
    RationalHeight (countedDisplay m H t x).1 (2*M) := by
  let a := min (max 0 (countedRetention t x/H)) 1
  change RationalHeight (countedMeshRound 1 m a).1 _
  unfold countedMeshRound
  split_ifs
  · exact rationalHeight_one.mono (Nat.zero_le _)
  · exact rationalHeight_zero.mono (Nat.zero_le _)
  · let q := countedMeshIndex 1 ((m:ℚ)*a) m
    have hq := rationalHeight_natCast q.1 M ((countedMeshIndex_index_le 1 ((m:ℚ)*a) m).trans hm)
    exact (((rationalHeight_one.div (rationalHeight_natCast m M hm)).mul hq).mono (by omega))

lemma countedOuterPrepare_displayed_height {n m : ℕ} (hm : 1≤m) (M : ℕ) (hM : m≤2^M)
    (cut : Fin m → Fin n → ℚ×ℚ) (pilot : Fin (outerPilotRounds m) → Fin n → ℚ×ℚ)
    (inner : Fin (2*m) → Fin n → ℚ×ℚ) (i : Fin n) (j : Fin (2*m)) :
    RationalHeight ((countedOuterPrepare hm cut pilot inner).displayed i j) (2*M) := by
  unfold countedOuterPrepare
  dsimp only
  split_ifs
  · exact rationalHeight_zero.mono (Nat.zero_le _)
  · let t := (countedCutoff hm cut).1
    let H := 1000*(countedPilot hm t pilot).1
    let f := fun (i : Fin n) (j : Fin (2*m)) => countedDisplay m H t (inner j i)
    let rows := Vector.ofFn fun i => Vector.ofFn (f i)
    change RationalHeight (((rows.get i).get j).1) _
    have hi : rows.get i = Vector.ofFn (f i) := Vector.getElem_ofFn i.isLt
    have hj : (Vector.ofFn (f i)).get j = f i j := Vector.getElem_ofFn j.isLt
    rw [hi,hj]
    exact countedDisplay_height H t (inner j i) M hM

def finiteMixtureAlphaHeight {n m : ℕ} (T : FairCallSchedule) (b Y M : ℕ) (y : Fin n → Fin m → ℚ) : ℕ :=
  let rows := empiricalStoredRows y
  let H := (rows.flatten.length+1)*(Y+4*M*rows.length+2)
  finiteFairBankOutputHeight n m Y M 0 (2*M+2) T.bits T.level + H+3*M+4+3*(m*(b+1)+M)+2

/-- In the scheduled preparation the rational sent to binary floor is the
selected interpolation fraction multiplied by the public dyadic size. -/
theorem countedFiniteCalibration_mixture_height {n m J : ℕ} (T P : FairCallSchedule) (b c : ℕ)
    (mu zlo zhi Lbar : ℚ) (y : Fin n → Fin m → ℚ) (x : Fin m → Fin n → ℚ)
    (bits : RankCalibrationBits n m J b c (T.Seed n) (P.Seed n)) (Y M : ℕ)
    (hm : m≤2^M) (hy : ∀ i j, RationalHeight (y i j) Y) :
    let d := countedDecodeRankCalibrationBits b c bits
    let q := countedCalibrationPrepare mu zlo zhi Lbar (countedFiniteTargetCall T y)
      (countedFiniteThresholdCall P y) y d.1.1
      (fun j => ((d.1.2.1 j).1,x j,(d.1.2.1 j).2.1,(d.1.2.1 j).2.2))
    let A := finiteMixtureAlphaHeight T b Y M y
    RationalHeight q.selection.2 A ∧
      RationalHeight (((2^c:ℕ):ℚ)*q.selection.2) (c+A) ∧
      RationalHeight (rationalMixtureGridRound (2^c) (by positivity) q.selection.2) c := by
  let d := countedDecodeRankCalibrationBits b c bits
  let v := fun j => ((d.1.2.1 j).1,x j,(d.1.2.1 j).2.1,(d.1.2.1 j).2.2)
  let E := finiteFairBankOutputHeight n m Y M 0 (2*M+2) T.bits T.level
  have hT (j : TargetGrid m) : RationalHeight (countedFiniteTargetCall T y ((j.val:ℚ)/(m:ℚ)) (d.1.1 j)).1 E :=
    countedFiniteTargetCall_height T y _ _ Y M (2*M+2) hm hy (targetGridCoefficient_height M hm j) (by omega)
  have hB (j : Fin m) (k : Fin n) : RationalHeight ((v j).2.2.1 k) b := by
    let l := Vector.ofFn (fun j : Fin m => countedRationalRankValidation b (bits.2.1 j))
    have hget : l.get j = countedRationalRankValidation b (bits.2.1 j) := Vector.getElem_ofFn j.isLt
    change RationalHeight ((l.get j).1.2.1 k) b
    rw [hget]
    exact countedRationalRankClocks_height b (bits.2.1 j).2.1 k
  have h := countedCalibrationPrepare_mixing_height mu zlo zhi Lbar (countedFiniteTargetCall T y)
    (countedFiniteThresholdCall P y) y d.1.1 v M Y E b hm hy hT hB
  exact ⟨h,(rationalHeight_natCast (2^c) c le_rfl).mul h,gridPoint_height c _⟩

end ProphetSecretary.Statistics.Calibration
