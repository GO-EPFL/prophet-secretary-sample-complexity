import ProphetSecretary.Analysis.BinaryFraction
import ProphetSecretary.Statistics.PlannerFairSeed

/-!
# Direct binary encoding of the dyadic reservoirs

The supplied bits are already the numerator's low-to-high digits. The
denominator is a one followed by the prescribed number of binary shifts.
No rational division is needed to construct the seed representation.
-/

namespace ProphetSecretary.Statistics
open ProphetSecretary.Analysis ProphetSecretary.Probability

def binaryPowerTwo (b : ℕ) : List Bool := List.replicate b false ++ [true]

lemma binaryPowerTwo_value (b : ℕ) : binaryWordValue (binaryPowerTwo b) = 2^b := by
  induction b with
  | zero => decide
  | succ b ih =>
    simp only [binaryPowerTwo,List.replicate_succ,List.cons_append,binaryWordValue,bitDigit,
      Bool.false_eq_true,if_false,zero_add,pow_succ] at ih ⊢
    rw [ih,Nat.mul_comm]

lemma binaryWordValue_ofFn_fairBits (b : ℕ) (bits : Fin b → Bool) :
    binaryWordValue (List.ofFn bits) = (fairBitsIndex b bits).val := by
  induction b with
  | zero => rfl
  | succ b ih =>
    rw [List.ofFn_succ]
    simp only [binaryWordValue,ih,fairBitsIndex,bitDigit]
    rw [Nat.add_comm]

def countedBinaryDyadicUniform (b : ℕ) (bits : Fin b → Bool) : BinaryFraction × ℕ :=
  (⟨false,List.ofFn bits,binaryPowerTwo b⟩,b)

lemma countedBinaryDyadicUniform_value (b : ℕ) (bits : Fin b → Bool) :
    (countedBinaryDyadicUniform b bits).1.value = (countedDyadicUniform b bits).1 := by
  simp [countedBinaryDyadicUniform,BinaryFraction.value,binaryPowerTwo_value,binaryWordValue_ofFn_fairBits,
    countedDyadicUniform,countedFairBitsIndex_value,gridPoint]

lemma countedBinaryDyadicUniform_width (b : ℕ) (bits : Fin b → Bool) :
    0 < binaryWordValue (countedBinaryDyadicUniform b bits).1.denominator ∧
      (countedBinaryDyadicUniform b bits).1.width ≤ b+1 := by
  constructor
  · change 0 < binaryWordValue (binaryPowerTwo b)
    rw [binaryPowerTwo_value]
    positivity
  · simp [countedBinaryDyadicUniform,BinaryFraction.width,binaryPowerTwo]

def binaryPlannerFairSeed {n : ℕ} (b : ℕ) (s : PlannerFairSeed n b) : PlannerFieldSeed n BinaryFraction :=
  plannerMapSeed (fun bits => (countedBinaryDyadicUniform b bits).1) s

lemma binaryPlannerFairSeed_value {n : ℕ} (b : ℕ) (s : PlannerFairSeed n b) :
    plannerMapSeed BinaryFraction.value (binaryPlannerFairSeed b s) = (countedPlannerFairSeed b s).1 := by
  simp only [binaryPlannerFairSeed,countedPlannerFairSeed,plannerMapSeed,countedBinaryDyadicUniform_value]

end ProphetSecretary.Statistics
