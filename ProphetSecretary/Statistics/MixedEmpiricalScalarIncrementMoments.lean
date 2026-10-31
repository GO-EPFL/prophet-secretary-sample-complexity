import ProphetSecretary.Statistics.MixedEmpiricalSlopeMomentRelations

/-!
# Uniform scalar-increment moments with exact known laws

For two fixed scalars, the normalized actual mixed residual difference has
second and sixth moments of orders k⁻¹ and k⁻³. The explicit constants are
uniform in the coefficient separation, finite instance size and known labels.
This is the unit-horizon form of `upstat:increments` for mixed designs.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.mixedSlopeSuffixMoment_two_uniform (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.mixedSlopeSuffixMoment known k z z' 2 ≤ 4 / (k : ℝ) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact (P.mixedSlopeSuffixMoment_two_le known hbound hz hzz).trans
    ((mul_le_mul_of_nonneg_left (P.mixedSlopeTruePremiumMoment_one_le_one known hbound hz hzz)
      (div_nonneg (by norm_num) hk)).trans_eq (mul_one _))

theorem Instance.mixedSlopeSuffixMoment_six_uniform (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.mixedSlopeSuffixMoment known k z z' 6 ≤
      (106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3 := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne k))
  have hb := P.mixedSlopeSuffixMoment_six_le (k := k) known hbound hz hzz
  have hU3 := P.mixedSlopeTruePremiumMoment_three_le (k := k) known hbound hz hzz
  have hU1 := P.mixedSlopeTruePremiumMoment_one_le_one (k := k) known hbound hz hzz
  have h35 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 5 := pow_le_pow_right₀ hk1 (by decide)
  have h36 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 6 := pow_le_pow_right₀ hk1 (by decide)
  have hInv5 : 1 / (k : ℝ) ^ 5 ≤ 1 / (k : ℝ) ^ 3 := by gcongr
  have hInv6 : 1 / (k : ℝ) ^ 6 ≤ 1 / (k : ℝ) ^ 3 := by gcongr
  have hAbs : P.mixedSlopeSuffixMoment known k z z' 6 ≤
      106000000000 * (1 : ℝ) ^ 3 / (k : ℝ) ^ 3 +
      106000000000 * Real.sqrt (P.mixedSlopeSuffixMoment known k z z' 6) / (k : ℝ) ^ 3 + 0 / (k : ℝ) ^ 6 := by
    calc
      _ ≤ 2000000000 * (P.mixedSlopeTruePremiumMoment known k z z' 3 / (k : ℝ) ^ 3 +
          P.mixedSlopeTruePremiumMoment known k z z' 1 / (k : ℝ) ^ 5) := hb
      _ ≤ 2000000000 * ((52 + 4 * Real.sqrt (P.mixedSlopeSuffixMoment known k z z' 6)) / (k : ℝ) ^ 3 +
          1 / (k : ℝ) ^ 5) := by gcongr
      _ ≤ 2000000000 * ((52 + 4 * Real.sqrt (P.mixedSlopeSuffixMoment known k z z' 6)) / (k : ℝ) ^ 3 +
          1 / (k : ℝ) ^ 3) := by gcongr
      _ ≤ _ := by
        have hp := div_nonneg (Real.sqrt_nonneg (P.mixedSlopeSuffixMoment known k z z' 6)) (pow_nonneg hk.le 3)
        ring_nf at hp ⊢
        nlinarith
  have h := ProphetSecretary.Statistics.absorb_sixth_moment
    (P.mixedSlopeSuffixMoment_nonnegative (k := k) known z z' 6) hk hAbs
  have hFinal := mul_le_mul_of_nonneg_left hInv6
    (sq_nonneg (106000000000 : ℝ))
  ring_nf at h hFinal ⊢
  linarith

end ProphetSecretary.Model
