import ProphetSecretary.Limiting.SharpTailHazardIntegral

/-!
# Sharp hazard domination through an actual clock marginal

An adaptive integrand may depend on more than its projected clock vector. A
uniform pointwise domination and the independent-uniform clock marginal are
sufficient for integrability and the sharp expected-error estimate.
-/

open MeasureTheory Set Filter
open scoped BigOperators Classical

namespace ProphetSecretary.Limiting

variable {N : ℕ} {Ω : Type*} [MeasurableSpace Ω]

theorem hazard_marginal_domination (ρ : Measure Ω) [IsProbabilityMeasure ρ]
    (T : Ω → ℝ) (U : Ω → Fin N → ℝ)
    (hTU : MeasurePreserving (fun q => (T q,U q)) ρ
      (Model.Instance.uniformClock.prod (Model.Instance.clocksLaw N)))
    (a : Fin N → ℝ) {B : ℝ} (hB : 0 ≤ B) (F : Ω → ℝ) (hF : Measurable F)
    (hdom : ∀ q, |F q| ≤ B * |tailHazardError a (T q) (U q)|) :
    Integrable F ρ ∧ |∫ q, F q ∂ρ| ≤ B * ((Real.pi / 2) * Real.sqrt (∑ i, a i ^ 2)) := by
  have hi : Integrable (fun q => B * |tailHazardError a (T q) (U q)|) ρ :=
    hTU.integrable_comp_of_integrable ((integrable_tailHazardError_product a).const_mul B)
  have hFI : Integrable F ρ := hi.mono' hF.aestronglyMeasurable
    (Filter.Eventually.of_forall fun q => by simpa only [Real.norm_eq_abs] using hdom q)
  have hmono := integral_mono hFI.abs hi hdom
  have hm : Measurable (fun z : ℝ × (Fin N → ℝ) => B * |tailHazardError a z.1 z.2|) :=
    (continuous_abs.measurable.comp (measurable_tailHazardError a)).const_mul B
  have he := integral_map (μ := ρ) hTU.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hTU.map_eq, integral_const_mul, integral_prod _ (integrable_tailHazardError_product a)] at he
  have hb := mul_le_mul_of_nonneg_left (integral_mean_abs_tailHazardError_sharp_le a) hB
  have hval : (∫ q, B * |tailHazardError a (T q) (U q)| ∂ρ) ≤
      B * ((Real.pi / 2) * Real.sqrt (∑ i, a i ^ 2)) := by
    exact he.symm.le.trans hb
  exact ⟨hFI, ((abs_integral_le_integral_abs (f := F)).trans hmono).trans hval⟩

end ProphetSecretary.Limiting
