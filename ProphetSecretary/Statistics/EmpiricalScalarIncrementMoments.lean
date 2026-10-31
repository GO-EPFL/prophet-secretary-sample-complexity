import ProphetSecretary.Statistics.EmpiricalSlopeMomentRelations

/-!
# Complete-path scalar increment moments

For two fixed scalar coefficients, normalization by their separation gives second
and sixth moments of order `k⁻¹` and `k⁻³`, respectively. Constants are explicit and
independent of the instance size and coefficient separation. This is the unit
remaining-horizon form of manuscript equation `upstat:increments`.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

theorem Instance.empiricalSlopeSuffixMoment_two_uniform (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.empiricalSlopeSuffixMoment k z z' 2 ≤ 4 / (k : ℝ) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  exact (P.empiricalSlopeSuffixMoment_two_le hbound hz hzz).trans
    ((mul_le_mul_of_nonneg_left (P.empiricalSlopeTruePremiumMoment_one_le_one hbound hz hzz)
      (div_nonneg (by norm_num) hk)).trans_eq (mul_one _))

theorem Instance.empiricalSlopeSuffixMoment_six_uniform (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') :
    P.empiricalSlopeSuffixMoment k z z' 6 ≤
      (106000000000 ^ 2 + 212000000000) / (k : ℝ) ^ 3 := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr (NeZero.ne k))
  have hb := P.empiricalSlopeSuffixMoment_six_le (k := k) hbound hz hzz
  have hU3 := P.empiricalSlopeTruePremiumMoment_three_le (k := k) hbound hz hzz
  have hU1 := P.empiricalSlopeTruePremiumMoment_one_le_one (k := k) hbound hz hzz
  have h35 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 5 := pow_le_pow_right₀ hk1 (by decide)
  have h36 : (k : ℝ) ^ 3 ≤ (k : ℝ) ^ 6 := pow_le_pow_right₀ hk1 (by decide)
  have hInv5 : 1 / (k : ℝ) ^ 5 ≤ 1 / (k : ℝ) ^ 3 := by gcongr
  have hInv6 : 1 / (k : ℝ) ^ 6 ≤ 1 / (k : ℝ) ^ 3 := by gcongr
  have hAbs : P.empiricalSlopeSuffixMoment k z z' 6 ≤
      106000000000 * (1 : ℝ) ^ 3 / (k : ℝ) ^ 3 +
      106000000000 * Real.sqrt (P.empiricalSlopeSuffixMoment k z z' 6) / (k : ℝ) ^ 3 + 0 / (k : ℝ) ^ 6 := by
    calc
      _ ≤ 2000000000 * (P.empiricalSlopeTruePremiumMoment k z z' 3 / (k : ℝ) ^ 3 +
          P.empiricalSlopeTruePremiumMoment k z z' 1 / (k : ℝ) ^ 5) := hb
      _ ≤ 2000000000 * ((52 + 4 * Real.sqrt (P.empiricalSlopeSuffixMoment k z z' 6)) / (k : ℝ) ^ 3 +
          1 / (k : ℝ) ^ 5) := by gcongr
      _ ≤ 2000000000 * ((52 + 4 * Real.sqrt (P.empiricalSlopeSuffixMoment k z z' 6)) / (k : ℝ) ^ 3 +
          1 / (k : ℝ) ^ 3) := by gcongr
      _ ≤ _ := by
        have hp := div_nonneg (Real.sqrt_nonneg (P.empiricalSlopeSuffixMoment k z z' 6)) (pow_nonneg hk.le 3)
        ring_nf at hp ⊢
        nlinarith
  have h := ProphetSecretary.Statistics.absorb_sixth_moment
    (P.empiricalSlopeSuffixMoment_nonnegative (k := k) z z' 6) hk hAbs
  have hFinal := mul_le_mul_of_nonneg_left hInv6
    (sq_nonneg (106000000000 : ℝ))
  ring_nf at h hFinal ⊢
  linarith

end ProphetSecretary.Model
