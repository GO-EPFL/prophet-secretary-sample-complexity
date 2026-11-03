import ProphetSecretary.Statistics.CalibratedCoefficientGrid
import ProphetSecretary.Probability.DyadicMixtureCoin
import Mathlib.Data.Rat.Floor

/-!
# Rational grid construction and probability rounding

The integer ceiling and floor used to form the coefficient grid and
rounded mixture threshold can be computed on rational values. Casting
these computations to the real model preserves their results.
-/

namespace ProphetSecretary.Statistics.Calibration
open ProphetSecretary.Probability

def rationalFamilyGridSize (m : ℕ) (zlo zhi : ℚ) : ℕ :=
  (Rat.ceil ((m : ℚ)*(zhi-zlo))).toNat

lemma rationalFamilyGridSize_eq (m : ℕ) (zlo zhi : ℚ) :
    rationalFamilyGridSize m zlo zhi=familyGridSize m (zlo : ℝ) (zhi : ℝ) := by
  unfold rationalFamilyGridSize familyGridSize
  rw [← Int.ceil_toNat]
  congr 1
  rw [Rat.ceil_eq_neg_floor_neg]
  change ⌈((m : ℚ)*(zhi-zlo))⌉=_
  simpa only [Rat.cast_mul,Rat.cast_sub,Rat.cast_natCast,Rat.ceil_cast] using
    (Rat.ceil_cast (α := ℝ) ((m : ℚ)*(zhi-zlo))).symm

def rationalMixtureGridIndex (N : ℕ) (hN : 0<N) (α : ℚ) : Fin N :=
  ⟨min (N-1) ((Rat.floor ((N : ℚ)*α)).toNat),lt_of_le_of_lt (min_le_left _ _) (by omega)⟩

def rationalMixtureGridRound (N : ℕ) (hN : 0<N) (α : ℚ) : ℚ :=
  gridPoint N (rationalMixtureGridIndex N hN α)

lemma rationalMixtureGridIndex_eq (N : ℕ) (hN : 0<N) (α : ℚ) :
    rationalMixtureGridIndex N hN α=uniformGridIndex N hN (α : ℝ) := by
  apply Fin.ext
  change min (N-1) ((Rat.floor ((N : ℚ)*α)).toNat) = min (N-1) ⌊(N : ℝ)*(α : ℝ)⌋₊
  rw [← Int.floor_toNat]
  have h : Rat.floor ((N : ℚ)*α)=⌊(N : ℝ)*(α : ℝ)⌋ := by
    change ⌊((N : ℚ)*α)⌋=_
    simpa only [Rat.cast_mul,Rat.cast_natCast] using
      (Rat.floor_cast (α := ℝ) ((N : ℚ)*α)).symm
  rw [h]

lemma rationalMixtureGridRound_cast (N : ℕ) (hN : 0<N) (α : ℚ) :
    (rationalMixtureGridRound N hN α : ℝ)=uniformGridRound N hN (α : ℝ) := by
  rw [rationalMixtureGridRound,gridPoint_ratCast,rationalMixtureGridIndex_eq]
  rfl

end ProphetSecretary.Statistics.Calibration
