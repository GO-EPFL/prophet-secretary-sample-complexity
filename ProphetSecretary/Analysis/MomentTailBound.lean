import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.GCongr
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

/-!
# Lower tail moments controlled by a higher moment

For a nonnegative error E, E^q 1{E≥r}≤E^p/r^(p−q). The integrability and
expectation bounds are explicit. The cases (p,q)=(6,1),(6,2) are used in
far-threshold and early-band losses in `upstat:selected`.
-/

open MeasureTheory Set Filter

namespace ProphetSecretary.Analysis

lemma pow_tail_le_higherMoment {e r : ℝ} (he : 0 ≤ e) (hr : 0 < r)
    {p q : ℕ} (hqp : q ≤ p) :
    (if r ≤ e then e ^ q else 0) ≤ e ^ p / r ^ (p - q) := by
  by_cases h : r ≤ e
  · rw [if_pos h]
    apply (le_div_iff₀ (pow_pos hr _)).mpr
    have hp : r ^ (p - q) ≤ e ^ (p - q) := by gcongr
    have hm := mul_le_mul_of_nonneg_left hp (pow_nonneg he q)
    have heq : e ^ q * e ^ (p - q) = e ^ p := by
      rw [← pow_add, show q + (p - q) = p by omega]
    exact hm.trans_eq heq
  · rw [if_neg h]
    exact div_nonneg (pow_nonneg he _) (pow_nonneg hr.le _)

theorem integral_pow_tail_le_higherMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {E : Ω → ℝ} (hE : Measurable E) (hnn : ∀ᵐ ω ∂μ, 0 ≤ E ω)
    {r : ℝ} (hr : 0 < r) {p q : ℕ} (hqp : q ≤ p)
    (hI : Integrable (fun ω => E ω ^ p) μ) :
    Integrable (fun ω => if r ≤ E ω then E ω ^ q else 0) μ ∧
      (∫ ω, if r ≤ E ω then E ω ^ q else 0 ∂μ) ≤ (∫ ω, E ω ^ p ∂μ) / r ^ (p - q) := by
  have hm : Measurable (fun ω => if r ≤ E ω then E ω ^ q else 0) :=
    Measurable.ite (measurableSet_le measurable_const hE) (hE.pow_const q) measurable_const
  have hDom : Integrable (fun ω => E ω ^ p / r ^ (p - q)) μ := hI.div_const _
  have hpoint : ∀ᵐ ω ∂μ, (if r ≤ E ω then E ω ^ q else 0) ≤ E ω ^ p / r ^ (p - q) :=
    hnn.mono fun _ hω => pow_tail_le_higherMoment hω hr hqp
  have hAbs : ∀ᵐ ω ∂μ, ‖if r ≤ E ω then E ω ^ q else 0‖ ≤ E ω ^ p / r ^ (p - q) := by
    filter_upwards [hnn, hpoint] with ω hω hpω
    have hpos : 0 ≤ if r ≤ E ω then E ω ^ q else 0 := by
      split_ifs
      · exact pow_nonneg hω _
      · exact le_rfl
    simpa only [Real.norm_eq_abs, abs_of_nonneg hpos] using hpω
  have htailI := hDom.mono' hm.aestronglyMeasurable hAbs
  refine ⟨htailI, ?_⟩
  have hint := integral_mono_ae htailI hDom hpoint
  rw [integral_div] at hint
  exact hint

/-- The entrance-size multiplier may depend on the same randomness as E;
only its nonnegativity and the actual weighted moment are used. -/
theorem integral_weighted_pow_tail_le_higherMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {E W : Ω → ℝ} (hE : Measurable E) (hW : Measurable W)
    (hnn : ∀ᵐ ω ∂μ, 0 ≤ E ω) (hWnn : ∀ᵐ ω ∂μ, 0 ≤ W ω)
    {r : ℝ} (hr : 0 < r) {p q : ℕ} (hqp : q ≤ p)
    (hI : Integrable (fun ω => W ω * E ω ^ p) μ) :
    Integrable (fun ω => W ω * (if r ≤ E ω then E ω ^ q else 0)) μ ∧
      (∫ ω, W ω * (if r ≤ E ω then E ω ^ q else 0) ∂μ) ≤
        (∫ ω, W ω * E ω ^ p ∂μ) / r ^ (p - q) := by
  have hm : Measurable (fun ω => W ω * (if r ≤ E ω then E ω ^ q else 0)) :=
    hW.mul (Measurable.ite (measurableSet_le measurable_const hE) (hE.pow_const q) measurable_const)
  have hDom : Integrable (fun ω => (W ω * E ω ^ p) / r ^ (p - q)) μ := hI.div_const _
  have hpoint : ∀ᵐ ω ∂μ, W ω * (if r ≤ E ω then E ω ^ q else 0) ≤
      (W ω * E ω ^ p) / r ^ (p - q) := by
    filter_upwards [hnn, hWnn] with ω he hw
    have h := mul_le_mul_of_nonneg_left (pow_tail_le_higherMoment he hr hqp) hw
    simpa only [mul_div_assoc] using h
  have hAbs : ∀ᵐ ω ∂μ, ‖W ω * (if r ≤ E ω then E ω ^ q else 0)‖ ≤
      (W ω * E ω ^ p) / r ^ (p - q) := by
    filter_upwards [hnn, hWnn, hpoint] with ω he hw hp
    have htail : 0 ≤ if r ≤ E ω then E ω ^ q else 0 := by
      split_ifs
      · exact pow_nonneg he _
      · exact le_rfl
    simpa only [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hw htail)] using hp
  have hi := hDom.mono' hm.aestronglyMeasurable hAbs
  refine ⟨hi, ?_⟩
  have h := integral_mono_ae hi hDom hpoint
  rw [integral_div] at h
  exact h

end ProphetSecretary.Analysis
