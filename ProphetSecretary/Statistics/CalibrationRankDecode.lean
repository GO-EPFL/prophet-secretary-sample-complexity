import ProphetSecretary.Statistics.RankCalibrationBits
import ProphetSecretary.Statistics.PlannerRationalDecode
import ProphetSecretary.Probability.CountedArrivalOrder

/-!
# Stored rational rank data

Each key and clock coordinate is decoded once. Validation permutations
store both directions, and sorted clocks are stored as rational vectors
before any validation or online decision.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Probability

variable {n m J : ℕ}

private lemma rankVectorGet_ofFn {A : Type*} {d : ℕ} (f : Fin d → A) (i : Fin d) :
    (Vector.ofFn f).get i = f i := by
  simp [Vector.get]

private lemma rankVectorGet_map {A B : Type*} {d : ℕ} (f : A → B)
    (q : Vector A d) (i : Fin d) : (q.map f).get i = f (q.get i) := by
  simp [Vector.get]

def countedRankClockGrid (b : ℕ) (bits : RankCalibrationClockBits n b) :
    Vector (Fin (2^b)) n × ℕ :=
  let q := Vector.ofFn (fun i : Fin n => countedStoredFairBitsIndex b (bits i))
  (q.map Prod.fst, (∑ i : Fin n, (q.get i).2)+8*n+3)

lemma countedRankClockGrid_value (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (countedRankClockGrid b bits).1.get = fun i => (countedFairBitsIndex b (bits i)).1 := by
  funext i
  simp only [countedRankClockGrid, rankVectorGet_map, rankVectorGet_ofFn, countedStoredFairBitsIndex_value]

def rankClockGridWork (n b : ℕ) : ℕ := n*(8*b+11)+3

lemma countedRankClockGrid_work (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (countedRankClockGrid b bits).2 = rankClockGridWork n b := by
  simp [countedRankClockGrid, rankClockGridWork, rankVectorGet_ofFn, countedStoredFairBitsIndex_work]
  ring

def countedRationalValidationOrder (b : ℕ) (bits : RankCalibrationClockBits n b) :
    Equiv.Perm (Fin n) × ℕ :=
  let grid := countedRankClockGrid b bits
  let key := countedValidationKeyPermutation grid.1.get
  (vectorPermutation key.1, grid.2+5*key.2+8*(n+1)^2)

lemma countedRationalValidationOrder_value (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (countedRationalValidationOrder b bits).1 = (countedDyadicValidationPermutation b bits).1 := by
  simp only [countedRationalValidationOrder, countedRankClockGrid_value,
    vectorPermutation_eq, countedDyadicValidationPermutation]

def rationalValidationOrderWork (n b : ℕ) : ℕ := rankClockGridWork n b + 28*(n+1)^2

lemma countedRationalValidationOrder_work (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (countedRationalValidationOrder b bits).2 ≤ rationalValidationOrderWork n b := by
  have h := countedValidationKeyPermutation_work (countedRankClockGrid b bits).1.get
  simp only [countedRationalValidationOrder, countedRankClockGrid_work, rationalValidationOrderWork]
  omega

def countedRationalRankClocks (b : ℕ) (bits : RankCalibrationClockBits n b) : Vector ℚ n × ℕ :=
  let grid := countedRankClockGrid b bits
  let sorted := countedSortVector grid.1.get
  let denom := countedBitGridSize b
  let times := Vector.ofFn (fun i => ((sorted.1 i).val : ℚ) / denom.1)
  (times,grid.2+3*sorted.2+denom.2+8*(n+1)^2)

lemma countedRationalRankClocks_value (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (countedRationalRankClocks b bits).1.get = (countedDyadicSortedClocks b bits).1 := by
  funext i
  simp only [countedRationalRankClocks, rankVectorGet_ofFn, countedRankClockGrid_value,
    countedBitGridSize_value, countedDyadicSortedClocks, gridPoint]

def rationalRankClocksWork (n b : ℕ) : ℕ := rankClockGridWork n b+20*(n+1)^2+2*b+1

lemma countedRationalRankClocks_work (b : ℕ) (bits : RankCalibrationClockBits n b) :
    (countedRationalRankClocks b bits).2 ≤ rationalRankClocksWork n b := by
  have h := countedSortVector_work (countedRankClockGrid b bits).1.get
  simp only [countedRationalRankClocks, countedRankClockGrid_work, countedBitGridSize_work, rationalRankClocksWork]
  omega

abbrev RationalRankValidationAux (n J : ℕ) (P : Type) :=
  Equiv.Perm (Fin n) × ((Fin n → ℚ) × PolicyQueryArray n J P)

abbrev RationalRankCalibratedSeed (n m J : ℕ) (T P : Type) :=
  (TargetGrid m → T) × ((Fin m → RationalRankValidationAux n J P) ×
    ((Fin n → ℚ) × (PolicyQueryArray n J P × ℚ)))

def countedRationalRankValidation {P : Type} (b : ℕ) (p : RankCalibrationValidationBits n J b P) :
    RationalRankValidationAux n J P × ℕ :=
  let key := countedRationalValidationOrder b p.1
  let clock := countedRationalRankClocks b p.2.1
  ((key.1,clock.1.get,p.2.2),key.2+clock.2+4)

lemma countedRationalRankValidation_work {P : Type} (b : ℕ) (p : RankCalibrationValidationBits n J b P) :
    (countedRationalRankValidation b p).2 ≤ rationalValidationOrderWork n b+rationalRankClocksWork n b+4 :=
  Nat.add_le_add_right (Nat.add_le_add (countedRationalValidationOrder_work b p.1)
    (countedRationalRankClocks_work b p.2.1)) 4

def countedDecodeRankCalibrationBits {T P : Type} (b c : ℕ)
    (p : RankCalibrationBits n m J b c T P) : RationalRankCalibratedSeed n m J T P × ℕ :=
  let validation := Vector.ofFn (fun l : Fin m => countedRationalRankValidation b (p.2.1 l))
  let online := countedRationalRankClocks b p.2.2.1
  let coin := countedStoredDyadicUniform c p.2.2.2.2
  ((p.1,(fun l => (validation.get l).1),online.1.get,p.2.2.2.1,coin.1),
    (∑ l : Fin m, (validation.get l).2) + online.2 + coin.2 + 8*(m+1)+8)

noncomputable def rationalRankCalibratedSeedCast {T P : Type}
    (p : RationalRankCalibratedSeed n m J T P) : RankCalibratedSeed n m J T P :=
  (p.1, (fun l => ((p.2.1 l).1, (fun i => ((p.2.1 l).2.1 i : ℝ)),(p.2.1 l).2.2)),
    (fun i => (p.2.2.1 i : ℝ)),p.2.2.2.1,(p.2.2.2.2 : ℝ))

/-- Stored rational clocks and cached permutation directions give the
same rank data as the established interpretation of the raw bits. -/
theorem countedDecodeRankCalibrationBits_value {T P : Type} (b c : ℕ)
    (p : RankCalibrationBits n m J b c T P) :
    rationalRankCalibratedSeedCast (countedDecodeRankCalibrationBits b c p).1 =
      interpretRankCalibrationBits b c p := by
  simp only [rationalRankCalibratedSeedCast, countedDecodeRankCalibrationBits,
    rankVectorGet_ofFn, countedRationalRankValidation, countedRationalValidationOrder_value,
    countedRationalRankClocks_value, countedStoredDyadicUniform_value,
    interpretRankCalibrationBits, interpretRankValidationBits]

theorem countedDecodeRankCalibrationBits_work {T P : Type} (b c : ℕ)
    (p : RankCalibrationBits n m J b c T P) :
    (countedDecodeRankCalibrationBits b c p).2 ≤
      m*(rationalValidationOrderWork n b+rationalRankClocksWork n b+4) +
        rationalRankClocksWork n b+10*c+7+8*(m+1)+8 := by
  have hV : ∑ l : Fin m, (countedRationalRankValidation b (p.2.1 l)).2 ≤
      m*(rationalValidationOrderWork n b+rationalRankClocksWork n b+4) := by
    calc
      _ ≤ ∑ _l : Fin m, (rationalValidationOrderWork n b+rationalRankClocksWork n b+4) :=
        Finset.sum_le_sum (fun l _ => countedRationalRankValidation_work b (p.2.1 l))
      _ = _ := by simp
  have hO := countedRationalRankClocks_work b p.2.2.1
  simp only [countedDecodeRankCalibrationBits, rankVectorGet_ofFn, countedStoredDyadicUniform_work]
  omega

end ProphetSecretary.Statistics.Calibration
