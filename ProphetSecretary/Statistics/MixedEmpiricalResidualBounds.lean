import ProphetSecretary.Statistics.MixedEmpiricalResidual
import ProphetSecretary.Statistics.EmpiricalResidualBounds
import ProphetSecretary.Model.MixedEmpiricalThresholdMeasurability

/-!
# Measurable mixed residual envelopes and auxiliary bounds

Known marginals give exactly zero residuals. Unknown marginals give measurable
finite sample averages at the actual mixed continuation. Cap-one true and sample
laws imply the same finite-dimensional bound used only for integrability.
-/

open MeasureTheory
open scoped Classical BigOperators

namespace ProphetSecretary.Model

variable {n k : ℕ} [NeZero k] {Ω : Type*} [MeasurableSpace Ω]

lemma Instance.measurable_mixedTransitionResidual (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i l, Measurable (fun ω => y ω i l)) (hc : Measurable c) (hc0 : ∀ ω, 0≤c ω)
    (hu : ∀ i, Measurable (fun ω => u ω i)) (i : Fin n) :
    Measurable (fun ω => (mixedEmpiricalInstance P known (y ω)).transitionResidual P 1 (c ω) (u ω) i) := by
  by_cases hi : i∈known
  · simpa only [mixedEmpiricalInstance_transitionResidual_known_zero P known _ hi] using
      (measurable_const : Measurable (fun _ : Ω => (0:ℝ)))
  let T : Ω → ℝ := fun ω => (mixedEmpiricalInstance P known (y ω)).continuationAtArrival 1 (c ω) (fun _ => 0) (u ω) i
  have hT : Measurable T := measurable_mixedEmpirical_continuationAtArrival P hP known
    (w:=fun _ => 1) (x:=fun _ => fun _ => 0) hy measurable_const hc (fun _ => zero_lt_one) hc0
    (fun _ => measurable_const) hu i
  have hhat : Measurable (fun ω => (k:ℝ)⁻¹*∑ l : Fin k, max (max 0 (y ω i l)-T ω) 0) :=
    (Finset.measurable_sum _ (fun l _ => ((measurable_const.max (hy i l)).sub hT).max measurable_const)).const_mul _
  have htrue := (positivePremium_continuous (P.law i) (P.integrable_maximum_iff.mp hP i) 1).measurable.comp hT
  convert hhat.sub htrue using 1
  funext ω
  change positivePremium ((mixedEmpiricalInstance P known (y ω)).law i) 1 (T ω)-positivePremium (P.law i) 1 (T ω) = _
  rw [positivePremium,mixedEmpiricalInstance_integral_unknown P known (y ω) hi]
  simp only [one_mul]
  rfl

lemma Instance.measurable_mixedResidualSuffixEnvelope (P : Instance n)
    (hP : Integrable Instance.maximum P.valuesLaw) (known : Finset (Fin n))
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i l, Measurable (fun ω => y ω i l)) (hc : Measurable c) (hc0 : ∀ ω, 0≤c ω)
    (hu : ∀ i, Measurable (fun ω => u ω i)) :
    Measurable (fun ω => (mixedEmpiricalInstance P known (y ω)).residualSuffixEnvelope P 1 (c ω) (u ω)) :=
  ProphetSecretary.Statistics.measurable_suffixEnvelope hu
    (fun i => P.measurable_mixedTransitionResidual hP known hy hc hc0 hu i)

lemma Instance.mixedResidualSuffixEnvelope_le_card (P : Instance n)
    (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (known : Finset (Fin n))
    (y : Reservoir n k) (hy : ∀ i l, y i l≤1) {c : ℝ} (hc : 0≤c) (u : Fin n → ℝ) :
    (mixedEmpiricalInstance P known y).residualSuffixEnvelope P 1 c u≤n := by
  apply (ProphetSecretary.Statistics.suffixEnvelope_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _i : Fin n, (1:ℝ) := Finset.sum_le_sum fun i _ =>
      (mixedEmpiricalInstance P known y).abs_transitionResidual_le_one_unitBounds P
        (mixedEmpiricalInstance_bounded P known y zero_le_one hPbound hy) hPbound hc u i
    _ = _ := by simp

lemma Instance.integrable_mixedResidualSuffixEnvelope_pow (P : Instance n)
    (hPbound : ∀ i, ∀ᵐ x ∂P.law i, x≤1) (known : Finset (Fin n))
    (ν : Measure Ω) [IsProbabilityMeasure ν]
    {y : Ω → Reservoir n k} {c : Ω → ℝ} {u : Ω → Fin n → ℝ}
    (hy : ∀ i l, Measurable (fun ω => y ω i l)) (hc : Measurable c) (hc0 : ∀ ω, 0≤c ω)
    (hu : ∀ i, Measurable (fun ω => u ω i))
    (hybound : ∀ᵐ ω ∂ν, ∀ i l, y ω i l≤1) (p : ℕ) :
    Integrable (fun ω => (mixedEmpiricalInstance P known (y ω)).residualSuffixEnvelope P 1 (c ω) (u ω)^p) ν := by
  have hm := (P.measurable_mixedResidualSuffixEnvelope (P.integrable_maximum_of_bounded hPbound) known hy hc hc0 hu).pow_const p
  apply Integrable.of_bound hm.aestronglyMeasurable ((n:ℝ)^p)
  filter_upwards [hybound] with ω hω
  change ‖((mixedEmpiricalInstance P known (y ω)).residualSuffixEnvelope P 1 (c ω) (u ω))^p‖≤_
  have h0 : 0≤(mixedEmpiricalInstance P known (y ω)).residualSuffixEnvelope P 1 (c ω) (u ω) :=
    ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _
  rw [Real.norm_eq_abs,abs_of_nonneg (pow_nonneg h0 p)]
  exact pow_le_pow_left₀ (ProphetSecretary.Statistics.suffixEnvelope_nonnegative _ _)
    (P.mixedResidualSuffixEnvelope_le_card hPbound known (y ω) hω (hc0 ω) (u ω)) p

end ProphetSecretary.Model
