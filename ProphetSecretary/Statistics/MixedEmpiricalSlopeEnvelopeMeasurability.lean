import ProphetSecretary.Statistics.MixedEmpiricalSlopeSuffixBridge
import ProphetSecretary.Statistics.MixedEmpiricalSuffixMoments

/-!
# Mixed scalar-increment envelope measurability and integrability

All sample and clock dependencies are retained. The finite cardinality bound
is auxiliary to integrability; statistical estimates use the actual mixed
reverse martingale and keep constants uniform in the number of variables.
-/

open MeasureTheory
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k]
variable {Ω : Type*} [MeasurableSpace Ω]

lemma Instance.measurable_mixedResidualSlopeSuffixEnvelope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hz' : 0 ≤ z')
    {y : Ω → Reservoir n k} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hu : ∀ i, Measurable fun ω => u ω i) :
    Measurable fun ω => (mixedEmpiricalInstance P known (y ω)).residualSlopeSuffixEnvelope P z z' (u ω) := by
  apply ProphetSecretary.Statistics.measurable_suffixEnvelope hu
  intro i
  exact ((P.measurable_mixedTransitionResidual hP known hy measurable_const (fun _ => hz) hu i).sub
    (P.measurable_mixedTransitionResidual hP known hy measurable_const (fun _ => hz') hu i)).div_const _

lemma Instance.mixedResidualSlopeSuffixEnvelope_le_card (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (known : Finset (Fin n)) (y : Reservoir n k) (hy : ∀ i j, y i j ≤ 1)
    {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z') (u : Fin n → ℝ) :
    (mixedEmpiricalInstance P known y).residualSlopeSuffixEnvelope P z z' u ≤ 2 * n / (z' - z) := by
  apply (ProphetSecretary.Statistics.suffixEnvelope_sub_div_le u _ _ (sub_pos.mpr hzz)).trans
  apply div_le_div_of_nonneg_right _ (sub_nonneg.mpr hzz.le)
  have ha := P.mixedResidualSuffixEnvelope_le_card hbound known y hy hz u
  have hb := P.mixedResidualSuffixEnvelope_le_card hbound known y hy (hz.trans hzz.le) u
  simp only [Instance.residualSuffixEnvelope] at ha hb
  linarith

lemma Instance.integrable_mixedResidualSlopeSuffixEnvelope_pow (P : Instance n)
    (hbound : ∀ i, ∀ᵐ x ∂P.law i, x ≤ 1) (known : Finset (Fin n)) {z z' : ℝ} (hz : 0 ≤ z) (hzz : z < z')
    (ν : Measure Ω) [IsProbabilityMeasure ν] {y : Ω → Reservoir n k} {u : Ω → Fin n → ℝ}
    (hy : ∀ i j, Measurable fun ω => y ω i j) (hu : ∀ i, Measurable fun ω => u ω i)
    (hybound : ∀ᵐ ω ∂ν, ∀ i j, y ω i j ≤ 1) (r : ℕ) :
    Integrable (fun ω => (mixedEmpiricalInstance P known (y ω)).residualSlopeSuffixEnvelope P z z' (u ω) ^ r) ν := by
  have hm := (P.measurable_mixedResidualSlopeSuffixEnvelope (P.integrable_maximum_of_bounded hbound) known hz (hz.trans hzz.le) hy hu).pow_const r
  apply Integrable.of_bound hm.aestronglyMeasurable ((2 * n / (z' - z)) ^ r)
  filter_upwards [hybound] with ω hω
  have h0 : 0 ≤ (mixedEmpiricalInstance P known (y ω)).residualSlopeSuffixEnvelope P z z' (u ω) :=
    ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 r)]
  exact pow_le_pow_left₀ h0 (P.mixedResidualSlopeSuffixEnvelope_le_card hbound known (y ω) hω hz hzz (u ω)) r

end ProphetSecretary.Model
