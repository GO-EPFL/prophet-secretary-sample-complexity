import ProphetSecretary.Statistics.EmpiricalPremiumTotals
import ProphetSecretary.Statistics.ResidualComparison

/-!
# Jointly measurable empirical residual envelopes

The finite sample-average formula proves joint measurability in arrays, clocks, and
nonnegative coefficients. Unit offer bounds give a dimension-dependent envelope bound
used only for integrability; the concentration estimates have separate uniform constants.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.positivePremium_le_one_of_unitBound (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (i : Fin n) {θ : ℝ} (hθ : 0 ≤ θ) :
    positivePremium (P.law i) 1 θ ≤ 1 := by
  have hI := P.integrable_maximum_iff.mp (P.integrable_maximum_of_bounded hbound) i
  have hm : (∫ x, x ∂P.law i) ≤ 1 := by
    have h : (∫ x, x ∂P.law i) ≤ ∫ _x : ℝ, (1 : ℝ) ∂P.law i :=
      integral_mono_ae hI (integrable_const 1) (hbound i)
    simpa only [integral_const, probReal_univ, one_smul] using h
  exact (positivePremium_le_firstMoment (P.law i) hI (P.nonnegative i) zero_le_one hθ).trans (by simpa only [one_mul] using hm)

lemma Instance.abs_transitionResidual_le_one_unitBounds (Q P : Instance n)
    (hQbound : ∀ i, ∀ᵐ x ∂Q.law i, x ≤ 1) (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (u : Fin n → ℝ) (i : Fin n) :
    |Q.transitionResidual P 1 c u i| ≤ 1 := by
  let θ := Q.continuationAtArrival 1 c (fun _ => 0) u i
  have hθ : 0 ≤ θ := Q.continuationAtArrival_nonnegative (Q.integrable_maximum_of_bounded hQbound)
    zero_le_one hc _ u i
  have hq0 := positivePremium_nonnegative (Q.law i) 1 θ
  have hp0 := positivePremium_nonnegative (P.law i) 1 θ
  have hq1 := Q.positivePremium_le_one_of_unitBound hQbound i hθ
  have hp1 := P.positivePremium_le_one_of_unitBound hPbound i hθ
  change |positivePremium (Q.law i) 1 θ - positivePremium (P.law i) 1 θ| ≤ 1
  rw [abs_le]
  constructor <;> linarith

variable {k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

lemma Instance.measurable_empiricalTransitionResidual (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i) (i : Fin n) :
    Measurable fun ω => (totalEmpiricalInstance (y ω)).transitionResidual P 1 (c ω) (u ω) i := by
  let T : Ω → ℝ := fun ω => (totalEmpiricalInstance (y ω)).continuationAtArrival 1 (c ω) (fun _ => 0) (u ω) i
  have hT : Measurable T := measurable_empiricalContinuationAtArrival hy hc hc0 hu i
  have hhat : Measurable (fun ω => (k : ℝ)⁻¹ * ∑ j : Fin k, max (max 0 (y ω i j) - T ω) 0) :=
    (Finset.measurable_sum _ (fun j _ => ((measurable_const.max (hy i j)).sub hT).max measurable_const)).const_mul _
  have htrue := (positivePremium_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) 1).measurable.comp hT
  convert hhat.sub htrue using 1
  funext ω
  change positivePremium ((totalEmpiricalInstance (y ω)).law i) 1 (T ω) - positivePremium (P.law i) 1 (T ω) =
    (k : ℝ)⁻¹ * (∑ j : Fin k, max (max 0 (y ω i j) - T ω) 0) - positivePremium (P.law i) 1 (T ω)
  rw [positivePremium, totalEmpiricalInstance_integral]
  simp only [one_mul]

lemma Instance.measurable_empiricalResidualSuffixEnvelope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw)
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i) :
    Measurable fun ω => (totalEmpiricalInstance (y ω)).residualSuffixEnvelope P 1 (c ω) (u ω) :=
  ProphetSecretary.Statistics.measurable_suffixEnvelope hu
    (fun i => P.measurable_empiricalTransitionResidual hP hy hc hc0 hu i)

lemma Instance.empiricalResidualSuffixEnvelope_le_card (P : Instance n)
    (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (y : Reservoir n k)
    (hy : ∀ i j, y i j ≤ 1) {c : ℝ} (hc : 0 ≤ c) (u : Fin n → ℝ) :
    (totalEmpiricalInstance y).residualSuffixEnvelope P 1 c u ≤ n := by
  apply (ProphetSecretary.Statistics.suffixEnvelope_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      exact (totalEmpiricalInstance y).abs_transitionResidual_le_one_unitBounds P
        (totalEmpiricalInstance_bounded y zero_le_one hy) hPbound hc u i
    _ = n := by simp

/-- Bounded training entries suffice for all joint envelope moments. No centering
or statistical independence is claimed when the coefficient is data-selected. -/
lemma Instance.integrable_empiricalResidualSuffixEnvelope_pow (P : Instance n)
    (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (ν : Measure Ω) [IsProbabilityMeasure ν]
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hc : Measurable c) (hc0 : ∀ ω, 0 ≤ c ω)
    (hu : ∀ i, Measurable fun ω => u ω i)
    (hybound : ∀ᵐ ω ∂ν, ∀ i j, y ω i j ≤ 1) (r : ℕ) :
    Integrable (fun ω => (totalEmpiricalInstance (y ω)).residualSuffixEnvelope P 1 (c ω) (u ω) ^ r) ν := by
  have hm := (P.measurable_empiricalResidualSuffixEnvelope (P.integrable_maximum_of_bounded hPbound) hy hc hc0 hu).pow_const r
  apply Integrable.of_bound hm.aestronglyMeasurable ((n : ℝ) ^ r)
  filter_upwards [hybound] with ω hω
  have h0 : 0 ≤ (totalEmpiricalInstance (y ω)).residualSuffixEnvelope P 1 (c ω) (u ω) :=
    ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 r)]
  exact pow_le_pow_left₀ h0 (P.empiricalResidualSuffixEnvelope_le_card hPbound (y ω) hω (hc0 ω) (u ω)) r

end ProphetSecretary.Model
