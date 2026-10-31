import ProphetSecretary.Probability.EnumeratedConditionalGrid
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-!
# Countable observation-time conditional maxima

A finite grid is sorted for the martingale estimate and then an actual monotone
limit gives the maximum over any countable enumeration of times. The second
and sixth constants remain 4 and 13, independent of the integrability bound.
-/

open MeasureTheory Filter Set
open scoped Classical Topology

namespace ProphetSecretary.Probability

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ℱ : Filtration ℝ mΩ) (f : Ω → ℝ) (τ : ℕ → ℝ)

noncomputable def countableConditionalMaximum (ω : Ω) : ℝ := max 0 (⨆ j, |μ[f | ℱ (τ j)] ω|)

omit [IsProbabilityMeasure μ] in
lemma countableConditionalMaximum_nonnegative (ω : Ω) : 0 ≤ countableConditionalMaximum μ ℱ f τ ω := le_max_left _ _

omit [IsProbabilityMeasure μ] in
lemma measurable_countableConditionalMaximum : Measurable (countableConditionalMaximum μ ℱ f τ) := by
  apply measurable_const.max
  apply Measurable.iSup
  intro j
  have hc : StronglyMeasurable[ℱ (τ j)] (μ[f | ℱ (τ j)]) := stronglyMeasurable_condExp
  exact (continuous_abs.comp_stronglyMeasurable (hc.mono (ℱ.le (τ j)))).measurable

omit [IsProbabilityMeasure μ] in
lemma countableConditionalMaximum_bounded {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D) :
    ∀ᵐ ω ∂μ, countableConditionalMaximum μ ℱ f τ ω ≤ D := by
  have hall : ∀ᵐ ω ∂μ, ∀ j, |μ[f | ℱ (τ j)] ω| ≤ D :=
    ae_all_iff.mpr fun j => condExp_abs_bounded μ hD hbound
  exact hall.mono fun ω hω => max_le hD (ciSup_le hω)

omit [IsProbabilityMeasure μ] in
lemma countableConditionalMaximum_dominates {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D) :
    ∀ᵐ ω ∂μ, ∀ j, |μ[f | ℱ (τ j)] ω| ≤ countableConditionalMaximum μ ℱ f τ ω := by
  have hall : ∀ᵐ ω ∂μ, ∀ j, |μ[f | ℱ (τ j)] ω| ≤ D :=
    ae_all_iff.mpr fun j => condExp_abs_bounded μ hD hbound
  exact hall.mono fun ω hω j => (le_ciSup ⟨D, by rintro _ ⟨j,rfl⟩; exact hω j⟩ j).trans (le_max_right _ _)

omit [IsProbabilityMeasure μ] in
lemma runningMaximum_tendsto_conditionalMaximum {D : ℝ} (ω : Ω)
    (hbound : ∀ j, |μ[f | ℱ (τ j)] ω| ≤ D) :
    Tendsto (fun N => runningMaximum (fun j => |μ[f | ℱ (τ j)] ω|) N) atTop
      (𝓝 (countableConditionalMaximum μ ℱ f τ ω)) := by
  let X : ℕ → ℝ := fun j => |μ[f | ℱ (τ j)] ω|
  have hX : BddAbove (range X) := ⟨D, by rintro _ ⟨j,rfl⟩; exact hbound j⟩
  have hM : BddAbove (range (runningMaximum X)) := ⟨D, by rintro _ ⟨j,rfl⟩; exact runningMaximum_le hbound j⟩
  have hmono : Monotone (runningMaximum X) := monotone_nat_of_le_succ fun j => le_max_left _ _
  have heq : (⨆ N, runningMaximum X N) = ⨆ j, X j := by
    apply le_antisymm
    · exact ciSup_le fun N => runningMaximum_le (fun j => le_ciSup hX j) N
    · exact ciSup_le fun j => (le_runningMaximum X (show j ≤ j from le_rfl)).trans (le_ciSup hM j)
  have h0 : 0 ≤ ⨆ j, X j := (abs_nonneg _).trans (le_ciSup hX 0)
  change Tendsto (runningMaximum X) atTop (𝓝 (max 0 (⨆ j, X j)))
  rw [max_eq_right h0]
  simpa only [heq] using tendsto_atTop_ciSup hmono hM

/-- Countable Doob bound for the actual tower-property martingale. -/
theorem countableConditionalMaximum_moment {D : ℝ} (hD : 0 ≤ D)
    (hbound : ∀ᵐ ω ∂μ, ‖f ω‖ ≤ D) {p : ℕ} (hp : p=2 ∨ p=6)
    (hf : Integrable (fun ω => ‖f ω‖ ^ p) μ) :
    Integrable (fun ω => countableConditionalMaximum μ ℱ f τ ω ^ p) μ ∧
    (∫ ω, countableConditionalMaximum μ ℱ f τ ω ^ p ∂μ) ≤
      (if p=2 then 4 else 13) * ∫ ω, ‖f ω‖ ^ p ∂μ := by
  have hB := countableConditionalMaximum_bounded μ ℱ f τ hD hbound
  have hI : Integrable (fun ω => countableConditionalMaximum μ ℱ f τ ω ^ p) μ := by
    apply Integrable.of_bound ((measurable_countableConditionalMaximum μ ℱ f τ).pow_const p).aestronglyMeasurable (D^p)
    filter_upwards [hB] with ω hω
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (countableConditionalMaximum_nonnegative μ ℱ f τ ω) p)]
    exact pow_le_pow_left₀ (countableConditionalMaximum_nonnegative μ ℱ f τ ω) hω p
  refine ⟨hI, ?_⟩
  have hall : ∀ᵐ ω ∂μ, ∀ j, |μ[f | ℱ (τ j)] ω| ≤ D :=
    ae_all_iff.mpr fun j => condExp_abs_bounded μ hD hbound
  have hconv : Tendsto (fun N => ∫ ω, runningMaximum (fun j => |μ[f | ℱ (τ j)] ω|) N ^ p ∂μ) atTop
      (𝓝 (∫ ω, countableConditionalMaximum μ ℱ f τ ω ^ p ∂μ)) := by
    apply tendsto_integral_of_dominated_convergence (fun _ => D^p)
      (fun N => (integrable_enumerated_condExpMaximum_pow μ ℱ f τ hD hbound p N).aestronglyMeasurable)
      (integrable_const _)
    · intro N
      filter_upwards [hall] with ω hω
      rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (runningMaximum_nonnegative (fun _ => abs_nonneg _) N) p)]
      exact pow_le_pow_left₀ (runningMaximum_nonnegative (fun _ => abs_nonneg _) N) (runningMaximum_le hω N) p
    · exact hall.mono fun ω hω => (runningMaximum_tendsto_conditionalMaximum μ ℱ f τ ω hω).pow p
  exact le_of_tendsto hconv (Eventually.of_forall fun N => enumeratedConditionalMaximum_moment μ ℱ f τ hD hbound hp hf N)

end ProphetSecretary.Probability
