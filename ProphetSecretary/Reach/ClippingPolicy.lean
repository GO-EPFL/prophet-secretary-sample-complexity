import ProphetSecretary.Reach.TailLifting
import ProphetSecretary.Model.Duration
import ProphetSecretary.Reach.Robust
import ProphetSecretary.Model.HalfGuarantee

/-!
# Policy comparison behind clipping

This is the policy-level part of `lem:clipping`. A reached cap is accepted, and
reach dominates mean duration. The theorem compares this particular policy with
its lift; it does not assume or assert that the policy is scalar-optimal.
-/

open MeasureTheory
open scoped NNReal

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma optimalScalarValue_positive (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : 0 < optimalScalarValue P w c := by
  have hC : 0 < optimalCompetitiveRatio :=
    (by norm_num : (0 : ℝ) < 1 / 2).trans_le half_le_optimalCompetitiveRatio
  have hden : 0 < w * P.expectedMaximum + c :=
    (mul_pos hw hP.2).trans_le (le_add_of_nonneg_right hc)
  exact (mul_pos hC hden).trans_le (globalScalar_inequality_of_integrable P hP.1 hw.le hc)

/-- The clipping height, totalized by zero outside the nonnegative parameter domain. -/
noncomputable def Instance.clippingHeight (P : Instance n) (w c : ℝ) : ℝ≥0 :=
  Real.toNNReal (optimalScalarValue P w c / w)

lemma Instance.clippingHeight_coe (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) :
    (P.clippingHeight w c : ℝ) = optimalScalarValue P w c / w :=
  Real.coe_toNNReal _ (div_nonneg (optimalScalarValue_nonnegative P hP hw.le hc) hw.le)

lemma Instance.clippingHeight_positive (P : Instance n) (hP : P.HasPositiveFiniteMaximum)
    {w c : ℝ} (hw : 0 < w) (hc : 0 ≤ c) : 0 < P.clippingHeight w c :=
  Real.toNNReal_pos.mpr (div_pos (optimalScalarValue_positive P hP hw hc) hw)

noncomputable def Instance.clippedDurationCoefficient (P : Instance n) (H : ℝ≥0) (w c : ℝ) : ℝ :=
  c + w * P.tailSum H

lemma Instance.clippedDurationCoefficient_nonnegative (P : Instance n) (H : ℝ≥0)
    {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) : 0 ≤ P.clippedDurationCoefficient H w c :=
  add_nonneg hc (mul_nonneg hw (P.tailSum_nonnegative H))

lemma RandomizedPolicy.cap_pullback_scalar_lower (π : RandomizedPolicy n) (P : Instance n)
    (H : ℝ≥0) (hP : Integrable Instance.maximum P.valuesLaw) {w c d : ℝ} (hw : 0 ≤ w)
    (hacc : ∀ᵐ ω : π.World ∂(P.cap H).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1)
    (hq : ∀ i, π.expectedDuration (P.cap H) ≤ π.rule.reachProbability (P.cap H) π.seedLaw i) :
    π.scalarObjective (P.cap H) w d +
      (P.clippedDurationCoefficient H w c - d) * π.expectedDuration (P.cap H) ≤
      (π.pullbackValues (capValue H) (measurable_capValue H)).scalarObjective P w c := by
  have htail : π.expectedDuration (P.cap H) * P.tailSum H ≤
      ∑ i, π.rule.reachProbability (P.cap H) π.seedLaw i * ∫ x, tailValue H x ∂P.law i := by
    rw [Instance.tailSum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    exact mul_le_mul_of_nonneg_right (hq i)
      (integral_nonneg fun x => tailValue_nonnegative H x)
  have hwTail := mul_le_mul_of_nonneg_left htail hw
  rw [π.scalarObjective_eq (P.cap H) (P.cap_integrable_maximum H hP),
    RandomizedPolicy.scalarObjective_eq _ P hP,
    π.expectedReward_cap_pullback_eq_tail_gain P H hP hacc,
    ← π.expectedDuration_cap P H]
  unfold Instance.clippedDurationCoefficient
  nlinarith

lemma RandomizedPolicy.cap_pullback_scalar_strict (π : RandomizedPolicy n) (P : Instance n)
    (H : ℝ≥0) (hP : Integrable Instance.maximum P.valuesLaw) {w c d : ℝ} (hw : 0 ≤ w)
    (hacc : ∀ᵐ ω : π.World ∂(P.cap H).worldLaw π.seedLaw,
      π.rule.AcceptsReachedCap H ω.2.2 ω.1 ω.2.1)
    (hq : ∀ i, π.expectedDuration (P.cap H) ≤ π.rule.reachProbability (P.cap H) π.seedLaw i)
    (hd : d < P.clippedDurationCoefficient H w c) :
    π.scalarObjective (P.cap H) w d <
      (π.pullbackValues (capValue H) (measurable_capValue H)).scalarObjective P w c := by
  have hT := π.expectedDuration_positive (P.cap H)
  have hpos := mul_pos (sub_pos.mpr hd) hT
  exact (lt_add_of_pos_right _ hpos).trans_le (π.cap_pullback_scalar_lower P H hP hw hacc hq)

end ProphetSecretary.Model
