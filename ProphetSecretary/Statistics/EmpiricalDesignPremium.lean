import ProphetSecretary.Statistics.EmpiricalResidualBounds

/-!
# Measurable empirical-design premiums and values

The empirical transition integrals are literal sample averages. Joint measurability
and bounded-data integrability are established before applying the premium mean and
Kac identities and before averaging training-selected coefficients.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_empiricalUnstoppedPremium
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i) :
    Measurable fun ω => (totalEmpiricalInstance (y ω)).unstoppedPremium 1 (c ω) (u ω) := by
  apply Finset.measurable_sum
  intro i _
  let T : Ω → ℝ := fun ω => (totalEmpiricalInstance (y ω)).continuationAtArrival 1 (c ω) (fun _ => 0) (u ω) i
  have hT : Measurable T := measurable_empiricalContinuationAtArrival hy hc hc0 hu i
  have havg : Measurable (fun ω => (k : ℝ)⁻¹ * ∑ j : Fin k, max (max 0 (y ω i j) - T ω) 0) :=
    (Finset.measurable_sum _ (fun j _ => ((measurable_const.max (hy i j)).sub hT).max measurable_const)).const_mul _
  convert havg using 1
  funext ω
  change positivePremium ((totalEmpiricalInstance (y ω)).law i) 1 (T ω) = _
  rw [positivePremium, totalEmpiricalInstance_integral]
  simp only [one_mul]

lemma empiricalUnstoppedPremium_le_card (y : Reservoir n k) (hy : ∀ i j, y i j ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (u : Fin n → ℝ) :
    (totalEmpiricalInstance y).unstoppedPremium 1 c u ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalEmpiricalInstance y).positivePremium_le_one_of_unitBound
        (totalEmpiricalInstance_bounded _ zero_le_one hy) i
        ((totalEmpiricalInstance y).continuationAtArrival_nonnegative (totalEmpiricalInstance_integrable y) zero_le_one hc _ u i)
    _ = n := by simp

lemma integrable_empiricalUnstoppedPremium_pow (ν : Measure Ω) [IsProbabilityMeasure ν]
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i)
    (hybound : ∀ᵐ ω ∂ν, ∀ i j, y ω i j ≤ 1) (r : ℕ) :
    Integrable (fun ω => (totalEmpiricalInstance (y ω)).unstoppedPremium 1 (c ω) (u ω) ^ r) ν := by
  apply Integrable.of_bound ((measurable_empiricalUnstoppedPremium hy hc hc0 hu).pow_const r).aestronglyMeasurable ((n : ℝ) ^ r)
  filter_upwards [hybound] with ω hω
  have h0 := (totalEmpiricalInstance (y ω)).unstoppedPremium_nonnegative 1 (c ω) (u ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 r)]
  exact pow_le_pow_left₀ h0 (empiricalUnstoppedPremium_le_card (y ω) hω (hc0 ω) (u ω)) r

lemma integrable_empiricalScalarValue_pow_unit (ν : Measure Ω) [IsProbabilityMeasure ν]
    {y : Ω → Reservoir n k} {c : Ω → ℝ} (hy : ∀ i j, Measurable fun ω => y ω i j)
    (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω) {C : ℝ}
    (hcC : ∀ᵐ ω ∂ν, c ω ≤ C) (hybound : ∀ᵐ ω ∂ν, ∀ i j, y ω i j ≤ 1) (r : ℕ) :
    Integrable (fun ω => optimalScalarValue (totalEmpiricalInstance (y ω)) 1 (c ω) ^ r) ν := by
  have hm := measurable_optimalScalarValue_totalEmpirical (w := fun _ => 1) hy measurable_const hc
    (fun _ => by norm_num) hc0
  apply Integrable.of_bound (hm.pow_const r).aestronglyMeasurable ((1 + C) ^ r)
  filter_upwards [hcC, hybound] with ω hC hY
  let Q := totalEmpiricalInstance (y ω)
  have hQ := totalEmpiricalInstance_integrable (y ω)
  have h0 := optimalScalarValue_nonnegative Q hQ zero_le_one (hc0 ω)
  have h1 := optimalScalarValue_le_benchmark Q hQ zero_le_one (hc0 ω)
  have hM : Q.expectedMaximum ≤ 1 := Q.expectedMaximum_le_of_bounded zero_le_one (totalEmpiricalInstance_bounded _ zero_le_one hY)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 r)]
  apply pow_le_pow_left₀ h0
  nlinarith

end ProphetSecretary.Model
