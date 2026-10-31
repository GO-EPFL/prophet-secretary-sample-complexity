import ProphetSecretary.Statistics.MixedEmpiricalResidualBounds

/-!
# Mixed design premiums and value integrability

Exact known laws are integrated directly and unknown laws are finite sample
averages. Joint measurability and cap-supported integrability precede all Kac
and localized moment estimates.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_mixedUnstoppedPremium (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i) :
    Measurable fun ω => (mixedEmpiricalInstance P known (y ω)).unstoppedPremium 1 (c ω) (u ω) := by
  apply Finset.measurable_sum
  intro i _
  let T : Ω → ℝ := fun ω => (mixedEmpiricalInstance P known (y ω)).continuationAtArrival 1 (c ω) (fun _ => 0) (u ω) i
  have hT : Measurable T := measurable_mixedEmpirical_continuationAtArrival P hP known
    (w:=fun _ => 1) (x:=fun _ => fun _ => 0) hy measurable_const hc (fun _ => zero_lt_one) hc0 (fun _ => measurable_const) hu i
  by_cases hi : i∈known
  · have htrue := (positivePremium_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) 1).measurable.comp hT
    convert htrue using 1
    funext ω
    change positivePremium ((mixedEmpiricalInstance P known (y ω)).law i) 1 (T ω) = _
    rw [mixedEmpiricalInstance_law_known P known (y ω) hi]
    rfl
  · have havg : Measurable (fun ω => (k:ℝ)⁻¹*∑ l : Fin k, max (max 0 (y ω i l)-T ω) 0) :=
      (Finset.measurable_sum _ (fun l _ => ((measurable_const.max (hy i l)).sub hT).max measurable_const)).const_mul _
    convert havg using 1
    funext ω
    change positivePremium ((mixedEmpiricalInstance P known (y ω)).law i) 1 (T ω) = _
    rw [positivePremium,mixedEmpiricalInstance_integral_unknown P known (y ω) hi]
    simp only [one_mul]

lemma mixedUnstoppedPremium_le_card (P : Instance n)
    (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (known : Finset (Fin n)) (y : Reservoir n k) (hy : ∀ i j, y i j ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (u : Fin n → ℝ) :
    (mixedEmpiricalInstance P known y).unstoppedPremium 1 c u ≤ n := by
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (mixedEmpiricalInstance P known y).positivePremium_le_one_of_unitBound
        (mixedEmpiricalInstance_bounded P known y zero_le_one hPbound hy) i
        ((mixedEmpiricalInstance P known y).continuationAtArrival_nonnegative (mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hPbound) known y) zero_le_one hc _ u i)
    _ = n := by simp

lemma integrable_mixedUnstoppedPremium_pow (P : Instance n)
    (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (known : Finset (Fin n)) (ν : Measure Ω) [IsProbabilityMeasure ν]
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i)
    (hybound : ∀ᵐ ω ∂ν, ∀ i j, y ω i j ≤ 1) (r : ℕ) :
    Integrable (fun ω => (mixedEmpiricalInstance P known (y ω)).unstoppedPremium 1 (c ω) (u ω) ^ r) ν := by
  apply Integrable.of_bound ((measurable_mixedUnstoppedPremium P (P.integrable_maximum_of_bounded hPbound) known hy hc hc0 hu).pow_const r).aestronglyMeasurable ((n : ℝ) ^ r)
  filter_upwards [hybound] with ω hω
  have h0 := (mixedEmpiricalInstance P known (y ω)).unstoppedPremium_nonnegative 1 (c ω) (u ω)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 r)]
  exact pow_le_pow_left₀ h0 (mixedUnstoppedPremium_le_card P hPbound known (y ω) hω (hc0 ω) (u ω)) r

lemma integrable_mixedScalarValue_pow_unit (P : Instance n)
    (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (known : Finset (Fin n)) (ν : Measure Ω) [IsProbabilityMeasure ν]
    {y : Ω → Reservoir n k} {c : Ω → ℝ} (hy : ∀ i j, Measurable fun ω => y ω i j)
    (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω) {C : ℝ}
    (hcC : ∀ᵐ ω ∂ν, c ω ≤ C) (hybound : ∀ᵐ ω ∂ν, ∀ i j, y ω i j ≤ 1) (r : ℕ) :
    Integrable (fun ω => optimalScalarValue (mixedEmpiricalInstance P known (y ω)) 1 (c ω) ^ r) ν := by
  have hm := measurable_optimalScalarValue_mixedEmpirical P (P.integrable_maximum_of_bounded hPbound) known (w := fun _ => 1) hy measurable_const hc
    (fun _ => by norm_num) hc0
  apply Integrable.of_bound (hm.pow_const r).aestronglyMeasurable ((1 + C) ^ r)
  filter_upwards [hcC, hybound] with ω hC hY
  let Q := mixedEmpiricalInstance P known (y ω)
  have hQ := mixedEmpiricalInstance_integrable P (P.integrable_maximum_of_bounded hPbound) known (y ω)
  have h0 := optimalScalarValue_nonnegative Q hQ zero_le_one (hc0 ω)
  have h1 := optimalScalarValue_le_benchmark Q hQ zero_le_one (hc0 ω)
  have hM : Q.expectedMaximum ≤ 1 := Q.expectedMaximum_le_of_bounded zero_le_one (mixedEmpiricalInstance_bounded P known (y ω) zero_le_one hPbound hY)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 r)]
  apply pow_le_pow_left₀ h0
  nlinarith

end ProphetSecretary.Model
