import ProphetSecretary.Limiting.HybridHorizonContinuity
import ProphetSecretary.Model.Truncation

/-!
# Capping the offers of a finite-intensity hybrid instance

Individual and anonymous marks are capped at K. The terminal reward and the
certified ambient cap stay fixed. Positive K preserves positive anonymous
observations, so the mapped intensity requires no removal of zero points.
-/

open MeasureTheory Set Filter
open scoped NNReal Classical
namespace ProphetSecretary.Limiting.FiniteIntensityHybridInstance
variable {n : ℕ}

noncomputable def capAt (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) (hK : 0<K) : FiniteIntensityHybridInstance n where
  cap := B.cap
  terminal := B.terminal
  terminal_le_cap := B.terminal_le_cap
  individuals := B.individuals.cap K
  individual_bounded i := by
    apply (ae_map_iff (Model.measurable_capValue K).aemeasurable measurableSet_Iic).mpr
    filter_upwards [B.individual_bounded i] with x hx
    exact (min_le_left _ _).trans hx
  intensity := B.intensity.map (Model.capValue K)
  intensity_supported := by
    change ∀ᵐ x ∂(B.intensity : Measure ℝ).map (Model.capValue K), x∈Ioc (0:ℝ) B.cap
    apply (ae_map_iff (Model.measurable_capValue K).aemeasurable measurableSet_Ioc).mpr
    filter_upwards [B.intensity_supported] with x hx
    exact ⟨lt_min hx.1 hK,(min_le_left _ _).trans hx.2⟩

@[simp] lemma capAt_terminal (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) (hK : 0<K) :
    (B.capAt K hK).terminal=B.terminal := rfl

@[simp] lemma capAt_cap (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) (hK : 0<K) :
    (B.capAt K hK).cap=B.cap := rfl

lemma capAt_individual_bounded (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) (hK : 0<K) (i : Fin n) :
    ∀ᵐ x ∂(B.capAt K hK).individuals.law i, x≤(K:ℝ) :=
  B.individuals.cap_bounded K i

lemma capAt_intensity_bounded (B : FiniteIntensityHybridInstance n) (K : ℝ≥0) (hK : 0<K) :
    ∀ᵐ x ∂((B.capAt K hK).intensity : Measure ℝ), x≤(K:ℝ) := by
  change ∀ᵐ x ∂(B.intensity : Measure ℝ).map (Model.capValue K), x≤(K:ℝ)
  apply (ae_map_iff (Model.measurable_capValue K).aemeasurable measurableSet_Iic).mpr
  exact Eventually.of_forall fun _ => min_le_right _ _

end ProphetSecretary.Limiting.FiniteIntensityHybridInstance
