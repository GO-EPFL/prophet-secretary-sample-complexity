import ProphetSecretary.Statistics.PlannerDyadicBits
import ProphetSecretary.Analysis.BinaryRationalWork

/-!
# Exact binary decoding of fair words

A fair word is read as a little-endian numerator over a power-of-two
denominator. Normalization is performed once, before the stored dyadic
value is used in comparisons.
-/

open scoped BigOperators

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Analysis ProphetSecretary.Probability

def countedCanonicalFairWord (b : ℕ) (bits : Fin b → Bool) : BinaryRational × ℕ :=
  let q := countedBinaryDyadicUniform b bits
  let r := q.1.countedReduce
  let h := (countedBinaryDyadicUniform_width b bits).1
  (⟨r.1.normalizeSign,by
      rw [show r.1.normalizeSign=BinaryFraction.encode q.1.value from
        BinaryFraction.countedReduce_normalization q.1 h]
      rw [BinaryFraction.encode_value]⟩,
    q.2+r.2+5)

lemma countedCanonicalFairWord_value (b : ℕ) (bits : Fin b → Bool) :
    (countedCanonicalFairWord b bits).1.value=gridPoint (2^b) (fairBitsIndex b bits) := by
  unfold countedCanonicalFairWord
  dsimp only
  change (countedBinaryDyadicUniform b bits).1.countedReduce.1.normalizeSign.value=_
  rw [BinaryFraction.normalizeSign_value,
    ((countedBinaryDyadicUniform b bits).1.countedReduce_correct (countedBinaryDyadicUniform_width b bits).1).1,
    countedBinaryDyadicUniform_value]
  simp only [countedDyadicUniform,countedFairBitsIndex_value]

lemma countedCanonicalFairWord_height (b : ℕ) (bits : Fin b → Bool) :
    RationalHeight (countedCanonicalFairWord b bits).1.value b := by
  rw [countedCanonicalFairWord_value]
  unfold gridPoint
  have hn : 0<(2^b : ℕ) := by positivity
  have hden : ((2^b : ℕ) : ℤ) ≠ 0 := by exact_mod_cast hn.ne'
  have h := rationalHeight_of_fraction ((fairBitsIndex b bits).val : ℤ)
    ((2^b : ℕ) : ℤ) hden b (by simp) (by simp)
  simpa only [Int.cast_natCast] using h

lemma countedCanonicalFairWord_work (b : ℕ) (bits : Fin b → Bool) :
    (countedCanonicalFairWord b bits).2≤110*(b+2)^3 := by
  have h := (countedBinaryDyadicUniform b bits).1.countedReduce_work
  have hw := (countedBinaryDyadicUniform_width b bits).2
  have hd := Nat.pow_le_pow_left (show (countedBinaryDyadicUniform b bits).1.width+1≤b+2 by omega) 3
  have h' := h.trans (Nat.mul_le_mul_left 100 hd)
  have hb : b+2≤(b+2)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<b+2) (by omega : 1≤3)
  change b+(countedBinaryDyadicUniform b bits).1.countedReduce.2+5≤_
  omega

def countedCanonicalFairWords {n : ℕ} (b : ℕ) (bits : Fin n → Fin b → Bool) :
    (Fin n → BinaryRational) × ℕ :=
  let q := Vector.ofFn (fun i => countedCanonicalFairWord b (bits i))
  (fun i => (q.get i).1,(∑ i : Fin n, ((q.get i).2+3))+2)

private lemma vector_get_ofFn {A : Type*} {N : ℕ} (f : Fin N → A) (i : Fin N) :
    (Vector.ofFn f).get i=f i := Vector.getElem_ofFn i.isLt

lemma countedCanonicalFairWords_value {n : ℕ} (b : ℕ) (bits : Fin n → Fin b → Bool) (i : Fin n) :
    ((countedCanonicalFairWords b bits).1 i).value=gridPoint (2^b) (fairBitsIndex b (bits i)) := by
  simp only [countedCanonicalFairWords,vector_get_ofFn,countedCanonicalFairWord_value]

lemma countedCanonicalFairWords_work {n : ℕ} (b : ℕ) (bits : Fin n → Fin b → Bool) :
    (countedCanonicalFairWords b bits).2≤n*(110*(b+2)^3+3)+2 := by
  simp only [countedCanonicalFairWords,vector_get_ofFn]
  apply Nat.add_le_add_right
  calc
    _ ≤ ∑ _i : Fin n, (110*(b+2)^3+3) := by
      apply Finset.sum_le_sum
      intro i _
      exact Nat.add_le_add_right (countedCanonicalFairWord_work b (bits i)) 3
    _ = _ := by simp

end ProphetSecretary.Statistics.Calibration
