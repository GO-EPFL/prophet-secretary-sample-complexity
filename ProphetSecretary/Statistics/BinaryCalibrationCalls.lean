import ProphetSecretary.Statistics.BinaryFairBankCall
import ProphetSecretary.Statistics.FiniteBitWork

/-!
# Binary calibration queries

The target query uses the full set at horizon one. Continuation
queries enumerate the active unseen identities and use the finite
banks for the current rank and coefficient.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n m : ℕ}

def countedBinaryFiniteTargetCallAt (b R a : ℕ) (y : Fin n → Fin m → BinaryRational)
    (accuracy z : BinaryRational) (bits : FairQueryBank n b (2*a+1) R) : BinaryRational × ℕ :=
  let q := countedBinaryFairBankCall y (List.finRange n,1,z) b R a accuracy bits
  (q.value,q.work+n+3)

def countedBinaryFiniteTargetCall (s : FairCallSchedule) (y : Fin n → Fin m → BinaryRational)
    (accuracy z : BinaryRational) (bits : s.Seed n) : BinaryRational × ℕ :=
  countedBinaryFiniteTargetCallAt s.bits s.level (countedConfidenceLevel s.failure s.confidence).1
    y accuracy z bits

theorem countedBinaryFiniteTargetCall_value (s : FairCallSchedule) (y : Fin n → Fin m → BinaryRational)
    (accuracy z : BinaryRational) (ha : accuracy.value=s.accuracy) (bits : s.Seed n) :
    (countedBinaryFiniteTargetCall s y accuracy z bits).1.value =
      (countedFiniteTargetCall s (fun i j => (y i j).value) z.value bits).1 := by
  unfold countedBinaryFiniteTargetCall countedBinaryFiniteTargetCallAt countedFiniteTargetCall
  dsimp only
  rw [countedBinaryFairBankCall_value,ha]
  simp only [scalarPlannerStateValueMap,BinaryRational.one_value]

def countedBinaryFiniteThresholdCallAt (b R a : ℕ) (y : Fin n → Fin m → BinaryRational)
    (accuracy : BinaryRational) (A : Finset (Fin n)) (u z : BinaryRational)
    (bits : FairQueryBank n b (2*a+1) R) : BinaryRational × ℕ :=
  let l := countedPredicateFilter (fun i => i ∈ A) (List.finRange n)
  let q := countedBinaryFairBankCall y (l.1,u,z) b R a accuracy bits
  (q.value,q.work+l.2+10*(n+1)^2)

def countedBinaryFiniteThresholdCall (s : FairCallSchedule) (y : Fin n → Fin m → BinaryRational)
    (accuracy : BinaryRational) (A : Finset (Fin n)) (u z : BinaryRational)
    (bits : s.Seed n) : BinaryRational × ℕ :=
  countedBinaryFiniteThresholdCallAt s.bits s.level (countedConfidenceLevel s.failure s.confidence).1
    y accuracy A u z bits

theorem countedBinaryFiniteThresholdCall_value (s : FairCallSchedule) (y : Fin n → Fin m → BinaryRational)
    (accuracy : BinaryRational) (ha : accuracy.value=s.accuracy) (A : Finset (Fin n)) (u z : BinaryRational)
    (bits : s.Seed n) :
    (countedBinaryFiniteThresholdCall s y accuracy A u z bits).1.value =
      (countedFiniteThresholdCall s (fun i j => (y i j).value) A u.value z.value bits).1 := by
  unfold countedBinaryFiniteThresholdCall countedBinaryFiniteThresholdCallAt countedFiniteThresholdCall
  dsimp only
  rw [countedBinaryFairBankCall_value,ha]
  rfl

def binaryFiniteTargetCallWork (s : FairCallSchedule) (n m Y M Z H : ℕ) : ℕ :=
  binaryFairBankWorkBound n m Y M 0 Z s.bits s.level
    (countedConfidenceLevel s.failure s.confidence).1 H+n+3

def binaryFiniteThresholdCallWork (s : FairCallSchedule) (n m Y M U Z H : ℕ) : ℕ :=
  binaryFairBankWorkBound n m Y M U Z s.bits s.level
    (countedConfidenceLevel s.failure s.confidence).1 H+1+3*n+10*(n+1)^2

private lemma binaryOneHeight : RationalHeight (1:BinaryRational).value 0 := by
  rw [BinaryRational.one_value]
  exact rationalHeight_one

theorem countedBinaryFiniteTargetCall_bounds (s : FairCallSchedule) (y : Fin n → Fin m → BinaryRational)
    (accuracy z : BinaryRational) (bits : s.Seed n) (Y M Z H : ℕ)
    (hm : m≤2^M) (hy : ∀ i j, RationalHeight (y i j).value Y)
    (hz : RationalHeight z.value Z) (hZ : 2≤Z) (hh : RationalHeight accuracy.value H) :
    RationalHeight (countedBinaryFiniteTargetCall s y accuracy z bits).1.value
      (finiteFairBankOutputHeight n m Y M 0 Z s.bits s.level) ∧
      (countedBinaryFiniteTargetCall s y accuracy z bits).2≤binaryFiniteTargetCallWork s n m Y M Z H := by
  have hw := countedBinaryFairBankCall_work y (List.finRange n,1,z) s.bits s.level
    (countedConfidenceLevel s.failure s.confidence).1 accuracy bits Y M 0 Z H hm hy (List.nodup_finRange n)
    binaryOneHeight hz hZ hh
  have hv := countedBinaryFairBankCall_height y (List.finRange n,1,z) s.bits s.level accuracy s.failure s.confidence
    bits Y M 0 Z hm hy (List.nodup_finRange n) binaryOneHeight hz hZ
  exact ⟨hv,Nat.add_le_add_right (Nat.add_le_add_right hw n) 3⟩

theorem countedBinaryFiniteThresholdCall_bounds (s : FairCallSchedule) (y : Fin n → Fin m → BinaryRational)
    (accuracy : BinaryRational) (A : Finset (Fin n)) (u z : BinaryRational) (bits : s.Seed n)
    (Y M U Z H : ℕ) (hm : m≤2^M) (hy : ∀ i j,RationalHeight (y i j).value Y)
    (hu : RationalHeight u.value U) (hz : RationalHeight z.value Z) (hZ : 2≤Z) (hh : RationalHeight accuracy.value H) :
    RationalHeight (countedBinaryFiniteThresholdCall s y accuracy A u z bits).1.value
      (finiteFairBankOutputHeight n m Y M U Z s.bits s.level) ∧
      (countedBinaryFiniteThresholdCall s y accuracy A u z bits).2≤binaryFiniteThresholdCallWork s n m Y M U Z H := by
  let l := countedPredicateFilter (fun i => i∈A) (List.finRange n)
  have hL : l.1.Nodup := by
    unfold l
    rw [countedPredicateFilter_value]
    exact (List.nodup_finRange n).filter _
  have hW : l.2≤1+3*n := by
    simpa only [l,List.length_finRange] using
      countedPredicateFilter_work (fun i => i∈A) (List.finRange n)
  have hw := countedBinaryFairBankCall_work y (l.1,u,z) s.bits s.level
    (countedConfidenceLevel s.failure s.confidence).1 accuracy bits Y M U Z H hm hy hL hu hz hZ hh
  have hv := countedBinaryFairBankCall_height y (l.1,u,z) s.bits s.level accuracy s.failure s.confidence
    bits Y M U Z hm hy hL hu hz hZ
  refine ⟨hv,?_⟩
  unfold binaryFiniteThresholdCallWork
  change (countedBinaryFairBankCall y (l.1,u,z) s.bits s.level
    (countedConfidenceLevel s.failure s.confidence).1 accuracy bits).work+l.2+10*(n+1)^2≤_
  omega

end ProphetSecretary.Statistics.Calibration
