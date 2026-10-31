import ProphetSecretary.Model.ScalarQuadraticSupport
import ProphetSecretary.Analysis.AffineSlopeStability

/-!
# Reward-duration slope stability

Paper correspondence: `cor:dual`. Every general randomized online policy is
compared with any scalar-optimal policy at the base weight. A single explicit
constant works for every finite instance under the common offer cap.
-/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

noncomputable def scalarSlopeConstant (a b H : ℝ) : ℝ :=
  Real.sqrt (2 * (1 / ((a / 2) ^ 2 * (1 - (b + 1) / 2)) +
    2 * (H + 1) / (min a (1 - b) / 2) + 1))

lemma RandomizedPolicy.rewardDurationSlope_mem (π : RandomizedPolicy n) (P : Instance n)
    {H : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    π.expectedReward P - π.expectedDuration P ∈ Icc (-1 : ℝ) H := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hr0 := π.expectedReward_nonnegative P
  have hr1 := (π.expectedReward_le_maximum P hP).trans (P.expectedMaximum_le_of_bounded hH hbound)
  have ht0 := π.expectedDuration_nonnegative P
  have ht1 := π.expectedDuration_le_one P
  constructor <;> linarith

/-- Every optimizer has the same reward-duration slope at an interior weight.
The fixed-policy envelope, not a derivative of a policy choice, proves this. -/
lemma RandomizedPolicy.optimal_rewardDurationSlope_eq_deriv (π : RandomizedPolicy n) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {lam : ℝ} (hlam : lam ∈ Ioo (0 : ℝ) 1)
    (hopt : π.scalarObjective P lam (1 - lam) = optimalScalarValue P lam (1 - lam)) :
    π.expectedReward P - π.expectedDuration P = deriv (fun z ↦ optimalScalarValue P z (1 - z)) lam := by
  have h := π.stateWeight_envelope P hP (u := 1) zero_le_one hlam
    (by simpa only [mul_one] using hopt)
    (by simpa only [mul_one] using (P.scalarUnit_hasDerivAt hP hlam).differentiableAt)
  simpa only [mul_one, one_mul] using h.deriv.symm

/-- `cor:dual`, with a constant chosen before the finite instance, both policies,
and the interior scalar weight. Zero expected maximum is allowed. -/
theorem RandomizedPolicy.rewardDurationSlope_stability (π πopt : RandomizedPolicy n) (P : Instance n)
    {a b H lam : ℝ} (ha : 0 < a) (hb : b < 1) (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) (hlam : lam ∈ Icc a b)
    (hopt : πopt.scalarObjective P lam (1 - lam) = optimalScalarValue P lam (1 - lam)) :
    |(π.expectedReward P - π.expectedDuration P) - (πopt.expectedReward P - πopt.expectedDuration P)| ≤
      scalarSlopeConstant a b H * Real.sqrt (optimalScalarValue P lam (1 - lam) - π.scalarObjective P lam (1 - lam)) := by
  have hP := P.integrable_maximum_of_bounded hbound
  have hlam0 : lam ∈ Ioo (0 : ℝ) 1 := ⟨ha.trans_le hlam.1, hlam.2.trans_lt hb⟩
  let Bπ := π.expectedReward P - π.expectedDuration P
  let Bopt := πopt.expectedReward P - πopt.expectedDuration P
  let r := optimalScalarValue P lam (1 - lam) - π.scalarObjective P lam (1 - lam)
  let a' := a / 2
  let b' := (b + 1) / 2
  let d := min a (1 - b) / 2
  let K := 1 / (a' ^ 2 * (1 - b'))
  have ha' : 0 < a' := by dsimp [a']; positivity
  have hb' : b' < 1 := by dsimp [b']; linarith
  have hd : 0 < d := div_pos (lt_min ha (sub_pos.mpr hb)) (by norm_num)
  have hK : 0 ≤ K := by dsimp [K]; positivity
  have hr : 0 ≤ r := sub_nonneg.mpr (scalarObjective_le_optimal π P hP hlam0.1.le (sub_pos.mpr hlam0.2).le)
  have hBπ := π.rewardDurationSlope_mem P hH hbound
  have hBopt := πopt.rewardDurationSlope_mem P hH hbound
  have hBound : |Bπ - Bopt| ≤ H + 1 := by
    rw [abs_le]
    constructor <;> dsimp [Bπ, Bopt] <;> linarith [hBπ.1, hBπ.2, hBopt.1, hBopt.2]
  have hder : deriv (fun z ↦ optimalScalarValue P z (1 - z)) lam = Bopt :=
    (πopt.optimal_rewardDurationSlope_eq_deriv P hP hlam0 hopt).symm
  have hstep (h : ℝ) (hh : |h| ≤ d) : h * (Bπ - Bopt) ≤ r + K * h ^ 2 / 2 := by
    have hlower : -d ≤ h := (abs_le.mp hh).1
    have hupper : h ≤ d := (abs_le.mp hh).2
    have hda : d ≤ a / 2 := div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
    have hdb : d ≤ (1 - b) / 2 := div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    have hlam' : lam ∈ Icc a' b' := by constructor <;> dsimp [a', b'] <;> linarith [hlam.1, hlam.2]
    have hnew : lam + h ∈ Icc a' b' := by constructor <;> dsimp [a', b'] <;> linarith [hlam.1, hlam.2]
    have hnew0 : lam + h ∈ Ioo (0 : ℝ) 1 := ⟨ha'.trans_le hnew.1, hnew.2.trans_lt hb'⟩
    have hUpper := (P.scalarUnit_quadraticGap_uniform hP ha' hb' hlam' hnew).2
    rw [add_sub_cancel_left, hder] at hUpper
    have hComp := scalarObjective_le_optimal π P hP hnew0.1.le (sub_pos.mpr hnew0.2).le
    rw [π.scalarObjective_eq P hP] at hComp
    have hBase := π.scalarObjective_eq P hP lam (1 - lam)
    dsimp only [Bπ, Bopt, r, K] at *
    nlinarith
  exact ProphetSecretary.Analysis.slope_difference_le_sqrt hr hK (by linarith : 0 ≤ H + 1) hd hBound hstep

/-- Uniform quantifier order in `cor:dual`: the constant is chosen before the
instance size, distributions, weight, and general competing policies. -/
theorem scalarSlope_stability_uniform {a b H : ℝ} (ha : 0 < a) (hb : b < 1) (hH : 0 ≤ H) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (n : ℕ) (P : Instance n) (π πopt : RandomizedPolicy n) (lam : ℝ),
      (∀ i, ∀ᵐ x ∂P.law i, x ≤ H) → lam ∈ Icc a b →
      πopt.scalarObjective P lam (1 - lam) = optimalScalarValue P lam (1 - lam) →
      |(π.expectedReward P - π.expectedDuration P) - (πopt.expectedReward P - πopt.expectedDuration P)| ≤
        K * Real.sqrt (optimalScalarValue P lam (1 - lam) - π.scalarObjective P lam (1 - lam)) := by
  refine ⟨scalarSlopeConstant a b H, Real.sqrt_nonneg _, ?_⟩
  intro n P π πopt lam hbound hlam hopt
  exact π.rewardDurationSlope_stability πopt P ha hb hH hbound hlam hopt

end ProphetSecretary.Model
