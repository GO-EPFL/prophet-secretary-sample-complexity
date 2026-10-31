import ProphetSecretary.Reach.Constraint
import ProphetSecretary.Reach.Zeros

/-!
# Scalar consequences of a global reward guarantee

The guarantee is required only for positive finite expected maxima. Zero-mean
auxiliary instances are handled by nonnegative rewards. Padding by N observable
zero identities forces the expected duration up to the guaranteed ratio, with
the explicit universal error `20 / sqrt N`. Scalar targets remain analytical;
they are not observations supplied to the learner. This is the reward-to-scalar
transfer in `thm:bayes`.
-/

open MeasureTheory

namespace ProphetSecretary.Model

variable {n k N : ℕ}

lemma Learner.expectedReward_ge_of_guarantee (L : Learner n k) {ρ : ℝ}
    (hGuarantee : L.Guarantees ρ) (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) : ρ * P.expectedMaximum ≤ L.expectedReward P := by
  by_cases hM : 0 < P.expectedMaximum
  · exact hGuarantee P ⟨hP, hM⟩
  · have hzero : P.expectedMaximum = 0 := le_antisymm (not_lt.mp hM) P.expectedMaximum_nonnegative
    rw [hzero, mul_zero]
    exact (L.randomizedPolicy P).expectedReward_nonnegative P

lemma Instance.appendZeros_bounded (P : Instance n) {H : ℝ} (hH : 0 ≤ H)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H) :
    ∀ i, ∀ᵐ x ∂(P.appendZeros N).law i, x ≤ H := by
  intro i
  induction i using Fin.addCases with
  | left j => simpa only [Instance.appendZeros, Fin.addCases_left] using hbound j
  | right j =>
    simpa only [Instance.appendZeros, Fin.addCases_right, ae_dirac_eq, Filter.eventually_pure] using hH

/-- Explicit scalar guarantee after adding observable deterministic-zero offers.
Training remains adaptive and the budget holds on every outcome. -/
theorem Learner.padded_scalarObjective_ge (L : Learner (n + N) k) {ρ : ℝ}
    (hGuarantee : L.Guarantees ρ) (P : Instance n) {H w c : ℝ}
    (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hN : 0 < N) (hw : 0 ≤ w) (hc : 0 ≤ c) :
    ρ * (w * P.expectedMaximum + c) - 20 * c / Real.sqrt (N : ℝ) ≤
      (L.randomizedPolicy (P.appendZeros N)).scalarObjective (P.appendZeros N) w c := by
  let π := L.randomizedPolicy (P.appendZeros N)
  have hP := P.integrable_maximum_of_bounded hbound
  have hpad := P.appendZeros_bounded (N := N) hH hbound
  have hR := L.expectedReward_ge_of_guarantee hGuarantee (P.appendZeros N)
    (P.appendZeros_integrable_maximum N hP)
  rw [P.appendZeros_expectedMaximum N] at hR
  change ρ * P.expectedMaximum ≤ π.expectedReward (P.appendZeros N) at hR
  have hq (j : Fin N) : ρ ≤ π.rule.reachProbability (P.appendZeros N) π.seedLaw (Fin.natAdd n j) :=
    L.rare_jackpot_reach hGuarantee (P.appendZeros N) hH hpad (Fin.natAdd n j)
  have hT := π.rule.meanDuration_ge_common_zeroReach_sub_sqrt π.measurable_rule hN
    (P.appendZeros N) π.seedLaw ρ hq
  change ρ - 20 / Real.sqrt (N : ℝ) ≤ π.expectedDuration (P.appendZeros N) at hT
  have hRw := mul_le_mul_of_nonneg_left hR hw
  have hTc := mul_le_mul_of_nonneg_left hT hc
  rw [π.scalarObjective_eq (P.appendZeros N) (P.appendZeros_integrable_maximum N hP)]
  have heq : ρ * (w * P.expectedMaximum + c) - 20 * c / Real.sqrt (N : ℝ) =
      w * (ρ * P.expectedMaximum) + c * (ρ - 20 / Real.sqrt (N : ℝ)) := by ring
  rw [heq]
  exact add_le_add hRw hTc

/-- Lower bound on the scalar gap forced by a global `(C_PS-ε)` guarantee.
Both the sampling error and the zero-padding error have explicit constants. -/
theorem Learner.padded_scalarGap_ge (L : Learner (n + N) k) {ε : ℝ}
    (hGuarantee : L.Guarantees (optimalCompetitiveRatio - ε)) (P : Instance n)
    {H w c : ℝ} (hH : 0 ≤ H) (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ H)
    (hε : 0 ≤ ε) (hN : 0 < N) (hw : 0 ≤ w) (hc : 0 ≤ c) (hsum : w + c = 1) :
    -ε * (H + 1) - 20 / Real.sqrt (N : ℝ) ≤
      (L.randomizedPolicy (P.appendZeros N)).scalarObjective (P.appendZeros N) w c -
        optimalCompetitiveRatio * (w * P.expectedMaximum + c) := by
  have h := L.padded_scalarObjective_ge hGuarantee P hH hbound hN hw hc
  have hM := P.expectedMaximum_le_of_bounded hH hbound
  have hw1 : w ≤ 1 := by linarith
  have hc1 : c ≤ 1 := by linarith
  have hbase : w * P.expectedMaximum + c ≤ H + 1 := by
    have hMw := mul_le_mul_of_nonneg_left hM hw
    have hwH := mul_le_mul_of_nonneg_right hw1 hH
    linarith
  have hεbound := mul_le_mul_of_nonneg_left hbase hε
  have hzeroError : 20 * c / Real.sqrt (N : ℝ) ≤ 20 / Real.sqrt (N : ℝ) :=
    div_le_div_of_nonneg_right (by linarith : 20 * c ≤ 20) (Real.sqrt_nonneg _)
  nlinarith

end ProphetSecretary.Model
