import ProphetSecretary.Statistics.PlannerFairTape
import ProphetSecretary.Statistics.ScalarPlannerRationalQuery

/-!
# Arithmetic decoding of planner seeds

Read each bit once into a finite list, then form its dyadic numerator
by integer arithmetic. Store the three decoded coordinate vectors so
that the transition does not decode a coordinate again.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

variable {n : ℕ}

private def countedBitsNatural : List Bool → ℕ × ℕ
  | [] => (0,1)
  | a :: l =>
    let q := countedBitsNatural l
    (2*q.1 + if a then 1 else 0,q.2+5)

private lemma countedBitsNatural_work (l : List Bool) :
    (countedBitsNatural l).2 = 5*l.length+1 := by
  induction l <;> simp_all [countedBitsNatural]; omega

private lemma countedBitsNatural_value (b : ℕ) (bits : Fin b → Bool) :
    (countedBitsNatural (List.ofFn bits)).1 = (fairBitsIndex b bits).val := by
  induction b with
  | zero => rfl
  | succ b ih =>
    simp only [List.ofFn_succ, countedBitsNatural, ih, fairBitsIndex]

def countedBitGridSize : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | b+1 =>
    let q := countedBitGridSize b
    (2*q.1,q.2+2)

lemma countedBitGridSize_value (b : ℕ) :
    (countedBitGridSize b).1 = 2^b := by
  induction b <;> simp_all [countedBitGridSize, pow_succ, Nat.mul_comm]

lemma countedBitGridSize_work (b : ℕ) :
    (countedBitGridSize b).2 = 2*b+1 := by
  induction b <;> simp_all [countedBitGridSize]; omega

private def countedBitCoordinate (D b : ℕ) (bits : Fin b → Bool) : ℚ × ℕ :=
  let q := countedBitsNatural (List.ofFn bits)
  ((q.1 : ℚ)/D, q.2 + 3*b+3)

private lemma countedBitCoordinate_work (D b : ℕ) (bits : Fin b → Bool) :
    (countedBitCoordinate D b bits).2 = 8*b+4 := by
  rw [countedBitCoordinate, countedBitsNatural_work, List.length_ofFn]
  omega

private lemma countedBitCoordinate_value (b : ℕ) (bits : Fin b → Bool) :
    (countedBitCoordinate (countedBitGridSize b).1 b bits).1 = (countedDyadicUniform b bits).1 := by
  simp only [countedBitCoordinate, countedBitGridSize_value, countedBitsNatural_value,
    countedDyadicUniform, countedFairBitsIndex_value, gridPoint]

/-- Decode a stored vector of bits using an indexed read of each bit
and a single scan of the resulting list. -/
def countedStoredFairBitsIndex (b : ℕ) (bits : Fin b → Bool) : Fin (2^b) × ℕ :=
  let q := countedBitsNatural (List.ofFn bits)
  (⟨q.1, by dsimp only [q]; rw [countedBitsNatural_value]; exact (fairBitsIndex b bits).isLt⟩,
    q.2+3*b+2)

lemma countedStoredFairBitsIndex_value (b : ℕ) (bits : Fin b → Bool) :
    (countedStoredFairBitsIndex b bits).1 = (countedFairBitsIndex b bits).1 := by
  apply Fin.ext
  exact (countedBitsNatural_value b bits).trans (congrArg Fin.val (countedFairBitsIndex_value b bits).symm)

lemma countedStoredFairBitsIndex_work (b : ℕ) (bits : Fin b → Bool) :
    (countedStoredFairBitsIndex b bits).2 = 8*b+3 := by
  simp only [countedStoredFairBitsIndex, countedBitsNatural_work, List.length_ofFn]
  omega

def countedStoredDyadicUniform (b : ℕ) (bits : Fin b → Bool) : ℚ × ℕ :=
  let d := countedBitGridSize b
  let a := countedBitCoordinate d.1 b bits
  (a.1,d.2+a.2+2)

lemma countedStoredDyadicUniform_value (b : ℕ) (bits : Fin b → Bool) :
    (countedStoredDyadicUniform b bits).1 = (countedDyadicUniform b bits).1 :=
  countedBitCoordinate_value b bits

lemma countedStoredDyadicUniform_work (b : ℕ) (bits : Fin b → Bool) :
    (countedStoredDyadicUniform b bits).2 = 10*b+7 := by
  simp only [countedStoredDyadicUniform, countedBitGridSize_work, countedBitCoordinate_work]
  omega

def countedStoredPlannerFairSeed {n : ℕ} (b : ℕ) (seed : PlannerFairSeed n b) :
    PlannerFieldSeed n ℚ × ℕ :=
  let d := countedBitGridSize b
  let f := countedBitCoordinate d.1 b
  let first := f seed.1.1
  let firstCoins := Vector.ofFn (fun i => f (seed.1.2 i))
  let identity := f seed.2.1
  let times := Vector.ofFn (fun i => f (seed.2.2.1 i))
  let tailCoins := Vector.ofFn (fun i => f (seed.2.2.2 i))
  (((first.1, (firstCoins.map Prod.fst).get),
    (identity.1, ((times.map Prod.fst).get,(tailCoins.map Prod.fst).get))),
    d.2 + first.2 + (∑ i : Fin n, (firstCoins.get i).2) + identity.2 +
      (∑ i : Fin n, (times.get i).2) + (∑ i : Fin n, (tailCoins.get i).2) + 15*(n+1))

lemma countedStoredPlannerFairSeed_value (b : ℕ) (seed : PlannerFairSeed n b) :
    (countedStoredPlannerFairSeed b seed).1 = (countedPlannerFairSeed b seed).1 := by
  simp [countedStoredPlannerFairSeed, countedPlannerFairSeed, plannerMapSeed,
    Vector.get, countedBitCoordinate_value, funext_iff, Function.comp_def]

def plannerFairDecodeBound (n b : ℕ) : ℕ := (3*n+2)*(8*b+4) + 2*b+1 + 15*(n+1)

theorem countedStoredPlannerFairSeed_work (b : ℕ) (seed : PlannerFairSeed n b) :
    (countedStoredPlannerFairSeed b seed).2 = plannerFairDecodeBound n b := by
  simp [countedStoredPlannerFairSeed, plannerFairDecodeBound, Vector.get,
    countedBitGridSize_work, countedBitCoordinate_work, Finset.sum_const]
  ring

lemma countedStoredPlannerFairSeed_ratCast (b : ℕ) (seed : PlannerFairSeed n b) :
    plannerFieldSeedRatCast (countedStoredPlannerFairSeed b seed).1 = plannerFairSeedReal b seed := by
  rw [countedStoredPlannerFairSeed_value]
  rfl

end ProphetSecretary.Statistics
