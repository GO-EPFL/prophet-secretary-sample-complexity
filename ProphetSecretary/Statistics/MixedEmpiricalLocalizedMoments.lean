import ProphetSecretary.Statistics.MixedEmpiricalPremiumRelations

/-!
# Localized residual moments with exact known marginals

The actual mixed-law reverse martingale and Kac/premium identities close the
second and sixth moments at the true optimal scalar value. The explicit
constants are universal and uniform in the set of known identities.
-/

open MeasureTheory
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]

/-- The first-premium term in the sixth-moment budget is absorbed by its cubic
moment, including the small-sample remainder. -/
lemma Instance.mixedTruePremiumMoment_first_fifth_le (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedTruePremiumMoment known k z 1 / (k : ℝ) ^ 5 ≤
      P.mixedTruePremiumMoment known k z 3 / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6 := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  have hI1 := mixedTruePremium_joint_integrable_pow (k := k) P known hbound hz 1
  have hI3 := mixedTruePremium_joint_integrable_pow (k := k) P known hbound hz 3
  have hj : P.mixedTruePremiumMoment known k z 1 ^ 3 ≤ P.mixedTruePremiumMoment known k z 3 := by
    simpa only [Instance.mixedTruePremiumMoment, pow_one] using
      ProphetSecretary.Statistics.cube_integral_le_integral_cube
        ((P.trainingCoordinateLaw k).prod (Instance.clocksLaw n))
        (Filter.Eventually.of_forall (fun v =>
          (mixedEmpiricalInstance P known (reservoirCoordinates.symm v.1)).unstoppedPremiumUnder_nonnegative P 1 z v.2))
        (by simpa only [pow_one] using hI1) hI3
  exact (ProphetSecretary.Statistics.first_over_fifth_le_cube_over_third
      (P.mixedTruePremiumMoment_nonnegative (k := k) known z 1) hk).trans
    (add_le_add (div_le_div_of_nonneg_right hj (pow_nonneg hk.le 3)) le_rfl)

/-- Second-moment localization with the separate leading and remainder constants. -/
theorem Instance.mixedSuffixMoment_two_localized (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedSuffixMoment known k z 2 ≤ 8 * optimalScalarValue P 1 z / (k : ℝ) + 64 / (k : ℝ) ^ 2 := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  have hb := P.mixedSuffixMoment_two_le (k := k) known hbound hz
  have hu := P.mixedTruePremiumMoment_one_le (k := k) known hbound hz
  have hh : P.mixedSuffixMoment known k z 2 ≤
      (4 * optimalScalarValue P 1 z + 8 * Real.sqrt (P.mixedSuffixMoment known k z 2)) / (k : ℝ) := by
    calc
      _ ≤ (4 / (k : ℝ)) * P.mixedTruePremiumMoment known k z 1 := hb
      _ ≤ (4 / (k : ℝ)) * (optimalScalarValue P 1 z + 2 * Real.sqrt (P.mixedSuffixMoment known k z 2)) :=
        mul_le_mul_of_nonneg_left hu (div_nonneg (by norm_num) hk.le)
      _ = _ := by ring
  convert ProphetSecretary.Statistics.absorb_second_moment
    (P.mixedSuffixMoment_nonnegative (k := k) known z 2) hk hh using 1; norm_num

/-- Sixth-moment localization. The deliberately generous constants avoid any
instance-size dependence in the martingale and absorption steps. -/
theorem Instance.mixedSuffixMoment_six_localized (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedSuffixMoment known k z 6 ≤
      13344000000000 * optimalScalarValue P 1 z ^ 3 / (k : ℝ) ^ 3 +
        (6672000000000 ^ 2 + 4000000000) / (k : ℝ) ^ 6 := by
  have hk : (0 : ℝ) < k := Nat.cast_pos.mpr (NeZero.pos k)
  have hv : 0 ≤ optimalScalarValue P 1 z :=
    optimalScalarValue_nonnegative P (P.integrable_maximum_of_bounded hbound) zero_le_one hz
  have hb := P.mixedSuffixMoment_six_le (k := k) known hbound hz
  have hu := P.mixedTruePremiumMoment_three_le (k := k) known hbound hz
  have hf := P.mixedTruePremiumMoment_first_fifth_le (k := k) known hbound hz
  have hh : P.mixedSuffixMoment known k z 6 ≤
      6672000000000 * optimalScalarValue P 1 z ^ 3 / (k : ℝ) ^ 3 +
      6672000000000 * Real.sqrt (P.mixedSuffixMoment known k z 6) / (k : ℝ) ^ 3 +
      2000000000 / (k : ℝ) ^ 6 := by
    calc
      _ ≤ 2000000000 * (P.mixedTruePremiumMoment known k z 3 / (k : ℝ) ^ 3 +
          P.mixedTruePremiumMoment known k z 1 / (k : ℝ) ^ 5) := hb
      _ ≤ 2000000000 * (2 * (208 * optimalScalarValue P 1 z ^ 3 +
          1668 * Real.sqrt (P.mixedSuffixMoment known k z 6)) / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6) := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        calc
          _ ≤ 2 * P.mixedTruePremiumMoment known k z 3 / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6 := by
            ring_nf at hf ⊢
            linarith
          _ ≤ _ := by gcongr
      _ ≤ _ := by
        have hp := div_nonneg (pow_nonneg hv 3) (pow_nonneg hk.le 3)
        ring_nf at hp ⊢
        nlinarith
  convert ProphetSecretary.Statistics.absorb_sixth_moment
    (P.mixedSuffixMoment_nonnegative (k := k) known z 6) hk hh using 1; norm_num

/-- The manuscript's `upstat:localized`, with explicit universal constants for
both exponents used later in the statistical argument. -/
theorem Instance.mixedSuffixMoment_localized (P : Instance n) (known : Finset (Fin n))
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {z : ℝ} (hz : 0 ≤ z) :
    P.mixedSuffixMoment known k z 2 ≤
        64 * (optimalScalarValue P 1 z / (k : ℝ) + 1 / (k : ℝ) ^ 2) ∧
    P.mixedSuffixMoment known k z 6 ≤
        (6672000000000 ^ 2 + 13348000000000) *
          (optimalScalarValue P 1 z ^ 3 / (k : ℝ) ^ 3 + 1 / (k : ℝ) ^ 6) := by
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hv : 0 ≤ optimalScalarValue P 1 z :=
    optimalScalarValue_nonnegative P (P.integrable_maximum_of_bounded hbound) zero_le_one hz
  constructor
  · have h := P.mixedSuffixMoment_two_localized (k := k) known hbound hz
    have hp := div_nonneg hv hk
    ring_nf at h hp ⊢
    linarith
  · have h := P.mixedSuffixMoment_six_localized (k := k) known hbound hz
    have hp := div_nonneg (pow_nonneg hv 3) (pow_nonneg hk 3)
    have hp6 := div_nonneg (by norm_num : (0 : ℝ) ≤ 1) (pow_nonneg hk 6)
    ring_nf at h hp hp6 ⊢
    nlinarith

end ProphetSecretary.Model
