import ProphetSecretary.Statistics.PlannerPolynomialWeight
import Mathlib.Algebra.Order.Floor.Ring

/-!
# Accuracy levels for the scalar planner

The integer level makes the geometrically decaying squared error at most
`h²/64` after restoring the product weight. Its recursive tree size is
bounded explicitly by a constant times `(β/h)^8`.
-/

namespace ProphetSecretary.Statistics

noncomputable def plannerPrecisionSize (β h : ℝ) : ℕ :=
  Nat.ceil (1600 * β^2 / h^2)

noncomputable def plannerAccuracyLevel (β h : ℝ) : ℕ :=
  Nat.clog 2 (plannerPrecisionSize β h)

lemma plannerPrecisionSize_pos {β h : ℝ} (hβ : 1 ≤ β) (hh : 0 < h) :
    0 < plannerPrecisionSize β h := by
  apply Nat.ceil_pos.mpr
  positivity

/-- The chosen level meets the mean-square tolerance before confidence amplification. -/
theorem plannerAccuracyLevel_error {β h : ℝ} (hh : 0 < h) :
    25 * β^2 / (2 : ℝ)^(plannerAccuracyLevel β h) ≤ h^2/64 := by
  have hp : (0 : ℝ) < h^2 := sq_pos_of_pos hh
  have he : 1600 * β^2 / h^2 ≤ (2 : ℝ)^(plannerAccuracyLevel β h) := by
    calc
      _ ≤ (plannerPrecisionSize β h : ℝ) := Nat.le_ceil _
      _ ≤ _ := by exact_mod_cast Nat.le_pow_clog (by decide : 1 < 2) (plannerPrecisionSize β h)
  have hm := (div_le_iff₀ hp).mp he
  apply (div_le_iff₀ (by positivity : 0 < (2 : ℝ)^(plannerAccuracyLevel β h))).mpr
  nlinarith

/-- A concrete polynomial envelope for the recursive tree factor. -/
theorem plannerAccuracyLevel_work {β h : ℝ} (hβ : 1 ≤ β)
    (hh : h ∈ Set.Ioo (0 : ℝ) 1) :
    (16 : ℝ)^(plannerAccuracyLevel β h) ≤ (6400 : ℝ)^4 * (β/h)^8 := by
  let R := 1600 * β^2 / h^2
  have hR : 1 ≤ R := by
    dsimp [R]
    apply (le_div_iff₀ (sq_pos_of_pos hh.1)).mpr
    nlinarith [sq_nonneg (β-1), sq_nonneg h, mul_nonneg hh.1.le (sub_nonneg.mpr hh.2.le)]
  have hceil : (plannerPrecisionSize β h : ℝ) ≤ 2*R := by
    have hc := Nat.ceil_lt_add_one (show 0 ≤ R by linarith)
    change (Nat.ceil R : ℝ) ≤ 2*R
    linarith
  have hpow : (2 : ℝ)^(plannerAccuracyLevel β h) ≤ 4*R := by
    have hn := plannerPrecisionSize_pos hβ hh.1
    have hc : (2 : ℝ)^(Nat.clog 2 (plannerPrecisionSize β h)) ≤
        2 * (plannerPrecisionSize β h : ℝ) := by
      exact_mod_cast two_pow_clog_le_twice hn
    exact hc.trans (by linarith)
  calc
    (16 : ℝ)^(plannerAccuracyLevel β h) = ((2 : ℝ)^(plannerAccuracyLevel β h))^4 := by
      rw [← pow_mul, Nat.mul_comm, pow_mul]
      norm_num
    _ ≤ (4*R)^4 := pow_le_pow_left₀ (by positivity) hpow _
    _ = (6400 : ℝ)^4 * (β/h)^8 := by
      dsimp [R]
      field_simp
      ring

end ProphetSecretary.Statistics
