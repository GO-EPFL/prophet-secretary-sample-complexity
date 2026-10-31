import ProphetSecretary.Model.CompetitiveBasic
import ProphetSecretary.Reach.Robust
import ProphetSecretary.Model.ScalarCoefficientMeasurability

/-! # Unit bounds for the normalized scalar gap on cap-one instances -/

open MeasureTheory Set

namespace ProphetSecretary.Model

variable {n : ℕ}

lemma Instance.normalizedScalarGap_mem_unit (P : Instance n)
    (hcap : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) {a : ℝ} (ha : a∈Icc (0 : ℝ) 1) :
    normalizedScalarGap P a∈Icc (0 : ℝ) 1 := by
  have hP := P.integrable_maximum_of_bounded hcap
  have hM := P.expectedMaximum_le_of_bounded zero_le_one hcap
  have hB0 : 0 ≤ a*P.expectedMaximum+(1-a) :=
    add_nonneg (mul_nonneg ha.1 P.expectedMaximum_nonnegative) (sub_nonneg.mpr ha.2)
  have hB1 : a*P.expectedMaximum+(1-a) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_left hM ha.1
    linarith
  refine ⟨normalizedScalarGap_nonnegative P hP ha,?_⟩
  have hV := optimalScalarValue_le_benchmark P hP ha.1 (sub_nonneg.mpr ha.2)
  have hC := mul_nonneg optimalCompetitiveRatio_nonnegative hB0
  unfold normalizedScalarGap scalarGap
  linarith

lemma Instance.measurable_normalizedGap_of_weight (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) {Ω : Type*} [MeasurableSpace Ω]
    {L : Ω → ℝ} (hL : Measurable L) (hRange : ∀ ω, L ω∈Icc (0 : ℝ) 1) :
    Measurable (fun ω => normalizedScalarGap P (L ω)) := by
  have hV := P.measurable_scalarValue_coefficients hP hL (measurable_const.sub hL)
    (fun ω => (hRange ω).1) (fun ω => sub_nonneg.mpr (hRange ω).2)
  exact hV.sub (((hL.mul_const P.expectedMaximum).add (measurable_const.sub hL)).const_mul
    optimalCompetitiveRatio)

end ProphetSecretary.Model
