import ProphetSecretary.Reach.Dyadic
import ProphetSecretary.Probability.FourthMoment

/-!
# Expected dyadic empirical increments

Fourth moments give an explicit geometrically decaying bound for each finite level
maximum. All bounds are uniform in the sample count and the dyadic level.
-/

open MeasureTheory Set
open scoped BigOperators

namespace ProphetSecretary.Probability

lemma pow_four_add_le {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) : a ^ 4 + b ^ 4 ≤ (a + b) ^ 4 := by
  have h1 : 0 ≤ 4 * a ^ 3 * b := by positivity
  have h2 : 0 ≤ 6 * a ^ 2 * b ^ 2 := by positivity
  have h3 : 0 ≤ 4 * a * b ^ 3 := by positivity
  nlinarith

lemma dyadic_fourth_constant_le (j : ℕ) {r : ℝ} (hr : 0 < r) :
    (2 : ℝ) ^ j * ((1 / (2 : ℝ) ^ (j + 1)) / (r ^ 4) ^ 3 +
      3 * (1 / (2 : ℝ) ^ (j + 1)) ^ 2 / (r ^ 4) ^ 2) ≤
      (2 * (7 / 8 : ℝ) ^ j / r ^ 2 + 1 / r ^ 3) ^ 4 := by
  let d : ℝ := 2 ^ j
  let g : ℝ := (7 / 8) ^ j
  have hd : 0 < d := by dsimp [d]; positivity
  have hg : 0 ≤ g := by dsimp [g]; positivity
  have hdecay : 1 ≤ d * g ^ 4 := by
    have h := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by norm_num : (1 : ℝ) ≤ 2 * (7 / 8 : ℝ) ^ 4) j
    simpa only [d, g, one_pow, mul_pow, ← pow_mul, Nat.mul_comm] using h
  have hnum : 2 * d + 3 * r ^ 4 ≤ 4 * d * (16 * g ^ 4 * r ^ 4 + 1) := by
    have h := mul_le_mul_of_nonneg_right hdecay (pow_nonneg hr.le 4)
    nlinarith [pow_nonneg hr.le 4]
  calc
    _ = (2 * d + 3 * r ^ 4) / (4 * d * r ^ 12) := by
      dsimp [d]
      rw [pow_succ]
      field_simp [hr.ne']
      ring
    _ ≤ (4 * d * (16 * g ^ 4 * r ^ 4 + 1)) / (4 * d * r ^ 12) :=
      div_le_div_of_nonneg_right hnum (by positivity)
    _ = (2 * g / r ^ 2) ^ 4 + (1 / r ^ 3) ^ 4 := by
      field_simp [hr.ne', hd.ne']
      ring
    _ ≤ _ := pow_four_add_le (by positivity) (by positivity)

open ProphetSecretary.Reach.EmpiricalChaining ProphetSecretary.Reach.ZeroReach ProphetSecretary.Model.Instance

lemma empirical_levelIncrement_fourthMoment (N : ℕ) (hN : 0 < N) (j : ℕ)
    (k : Fin (2 ^ j)) :
    (∫ u : Fin N → ℝ, |levelIncrement (fun u => empiricalCDF u) j k u| ^ 4 ∂clocksLaw N) ≤
      (1 / (2 : ℝ) ^ (j + 1)) / (N : ℝ) ^ 3 +
        3 * (1 / (2 : ℝ) ^ (j + 1)) ^ 2 / (N : ℝ) ^ 2 := by
  have h := uniform_interval_empirical_fourthMoment N hN (gridPoint_nonnegative j k)
    (gridPoint_le_odd j k) (gridPoint_odd_le_one j k)
  rw [gridPoint_odd_gap] at h
  have he (u : Fin N → ℝ) :
      |levelIncrement (fun u => empiricalCDF u) j k u| ^ 4 =
      ((∑ i, (if gridPoint j k < u i ∧ u i ≤ gridPoint (j + 1) (2 * k.val + 1)
        then (1 : ℝ) else 0)) / (N : ℝ) - 1 / (2 : ℝ) ^ (j + 1)) ^ 4 := by
    rw [levelIncrement_eq, empiricalCDF_difference_eq_interval u (gridPoint_le_odd j k),
      ← abs_pow]
    exact abs_of_nonneg (by positivity)
  simpa only [he] using h

/-- The expected maximum at level `j` decays geometrically, apart from the explicitly
smaller finite-sample remainder. Here `r⁴=N`; no asymptotic notation is used. -/
lemma expected_empirical_levelMaximum (N : ℕ) (hN : 0 < N) (j : ℕ) {r : ℝ}
    (hr : 0 < r) (hrN : r ^ 4 = (N : ℝ)) :
    (∫ u : Fin N → ℝ, levelMaximum (fun u => empiricalCDF u) j u ∂clocksLaw N) ≤
      2 * (7 / 8 : ℝ) ^ j / r ^ 2 + 1 / r ^ 3 := by
  apply mean_maxAbs_le_of_fourth (clocksLaw N)
    (fun k => measurable_levelIncrement (fun t => measurable_empiricalCDF
      (fun i => measurable_pi_apply i) measurable_const) j k)
    (fun k => Filter.Eventually.of_forall (abs_empirical_levelIncrement_le_one hN id j k))
    (by positivity)
  calc
    _ ≤ ∑ _k : Fin (2 ^ j), ((1 / (2 : ℝ) ^ (j + 1)) / (N : ℝ) ^ 3 +
        3 * (1 / (2 : ℝ) ^ (j + 1)) ^ 2 / (N : ℝ) ^ 2) :=
      Finset.sum_le_sum fun k _ => empirical_levelIncrement_fourthMoment N hN j k
    _ = (2 : ℝ) ^ j * ((1 / (2 : ℝ) ^ (j + 1)) / (r ^ 4) ^ 3 +
        3 * (1 / (2 : ℝ) ^ (j + 1)) ^ 2 / (r ^ 4) ^ 2) := by
      rw [hrN]
      simp
      ring
    _ ≤ _ := dyadic_fourth_constant_le j hr

end ProphetSecretary.Probability
