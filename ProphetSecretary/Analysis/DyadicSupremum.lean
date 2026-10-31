import ProphetSecretary.Analysis.DyadicMoments
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

/-! # A measurable version of the continuous supremum
The definition uses a countable dyadic supremum and a zero sentinel. On every
bounded continuous sample path it equals the actual interval supremum.
-/
open MeasureTheory Set Filter
open scoped BigOperators Topology Classical
namespace ProphetSecretary.Analysis
open ProphetSecretary.Reach.EmpiricalChaining
variable {Ω : Type*}

noncomputable def dyadicSupremum (f : Ω → ℝ → ℝ) (ω : Ω) : ℝ :=
  max 0 (⨆ j : ℕ, gridMaximum (liftProcess f) j ω)

lemma dyadicSupremum_nonnegative (f : Ω → ℝ → ℝ) (ω : Ω) : 0 ≤ dyadicSupremum f ω := le_max_left _ _

lemma dyadicSupremum_mem_Icc {f : Ω → ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D) (ω : Ω)
    (hBound : ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) : dyadicSupremum f ω ∈ Icc (0 : ℝ) D := by
  refine ⟨dyadicSupremum_nonnegative _ _, max_le hD ?_⟩
  exact ciSup_le (fun j ↦ lifted_gridMaximum_bound hD ω hBound j)

lemma lifted_gridMaximum_tendsto_supremum {f : Ω → ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D) (ω : Ω)
    (hBound : ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) :
    Tendsto (fun j ↦ gridMaximum (liftProcess f) j ω) atTop (𝓝 (dyadicSupremum f ω)) := by
  have hBdd : BddAbove (range (fun j ↦ gridMaximum (liftProcess f) j ω)) :=
    ⟨D, by rintro _ ⟨j, rfl⟩; exact lifted_gridMaximum_bound hD ω hBound j⟩
  have h0 : 0 ≤ ⨆ j : ℕ, gridMaximum (liftProcess f) j ω :=
    (maxAbs_nonnegative _ _).trans (le_ciSup hBdd 0)
  simpa only [dyadicSupremum, max_eq_right h0] using tendsto_atTop_ciSup (gridMaximum_monotone (liftProcess f) ω) hBdd

lemma dyadicSupremum_eq_intervalSup {f : Ω → ℝ → ℝ} {D : ℝ} (hD : 0 ≤ D) (ω : Ω)
    (hBound : ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) (hCont : ContinuousOn (f ω) (Icc (0 : ℝ) 1)) :
    dyadicSupremum f ω = sSup {y : ℝ | ∃ t ∈ Icc (0 : ℝ) 1, y = |f ω t|} := by
  let S : Set ℝ := {y : ℝ | ∃ t ∈ Icc (0 : ℝ) 1, y = |f ω t|}
  have hS : S.Nonempty := ⟨|f ω 0|, 0, ⟨le_rfl, zero_le_one⟩, rfl⟩
  have hSBdd : BddAbove S := ⟨D, by rintro y ⟨t, ht, rfl⟩; exact hBound t ht⟩
  have hS0 : 0 ≤ sSup S := (abs_nonneg _).trans (le_csSup hSBdd ⟨0, ⟨le_rfl, zero_le_one⟩, rfl⟩)
  have hGBdd : BddAbove (range (fun j ↦ gridMaximum (liftProcess f) j ω)) :=
    ⟨D, by rintro _ ⟨j, rfl⟩; exact lifted_gridMaximum_bound hD ω hBound j⟩
  apply le_antisymm
  · apply max_le hS0
    apply ciSup_le
    intro j
    apply maxAbs_le hS0
    intro k
    rw [lifted_gridDeviation]
    exact le_csSup hSBdd ⟨gridPoint j k, gridPoint_mem_unitInterval j k, rfl⟩
  · apply csSup_le hS
    rintro y ⟨t, ht, rfl⟩
    apply continuousOn_le_of_dyadic_bounds hCont _ t ht
    intro j k
    have hG := (le_maxAbs (fun k : Fin (2 ^ j + 1) ↦ gridDeviation (liftProcess f) j k) ω k).trans (le_ciSup hGBdd j)
    have hG' : |f ω (gridPoint j k)| ≤ ⨆ j : ℕ, gridMaximum (liftProcess f) j ω := by
      simpa only [lifted_gridDeviation] using hG
    exact hG'.trans (le_max_right 0 _)

variable [MeasurableSpace Ω]

lemma measurable_dyadicSupremum {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) :
    Measurable (dyadicSupremum f) := measurable_const.max (Measurable.iSup (fun j ↦ lifted_gridMaximum_measurable hf j))

lemma integrable_dyadicSupremum_pow (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) {D : ℝ} (hD : 0 ≤ D)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) (p : ℕ) :
    Integrable (fun ω ↦ dyadicSupremum f ω ^ p) μ :=
  integrable_nonnegative_pow_of_bound μ (measurable_dyadicSupremum hf) (dyadicSupremum_nonnegative f)
    (hBound.mono (fun ω hω ↦ (dyadicSupremum_mem_Icc hD ω hω).2)) p

lemma integral_lifted_gridMaximum_pow_tendsto (μ : Measure Ω) [IsFiniteMeasure μ]
    {f : Ω → ℝ → ℝ} (hf : ∀ t, Measurable (fun ω ↦ f ω t)) {D : ℝ} (hD : 0 ≤ D)
    (hBound : ∀ᵐ ω ∂μ, ∀ t ∈ Icc (0 : ℝ) 1, |f ω t| ≤ D) (p : ℕ) :
    Tendsto (fun j ↦ ∫ ω, gridMaximum (liftProcess f) j ω ^ p ∂μ) atTop
      (𝓝 (∫ ω, dyadicSupremum f ω ^ p ∂μ)) := by
  apply tendsto_integral_of_dominated_convergence (fun _ ↦ D ^ p)
    (fun j ↦ ((lifted_gridMaximum_measurable hf j).pow_const p).aestronglyMeasurable) (integrable_const _)
  · intro j
    filter_upwards [hBound] with ω hω
    have hNon : 0 ≤ gridMaximum (liftProcess f) j ω := maxAbs_nonnegative _ _
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hNon p)]
    exact pow_le_pow_left₀ (maxAbs_nonnegative _ _) (lifted_gridMaximum_bound hD ω hω j) p
  · exact hBound.mono (fun ω hω ↦ (lifted_gridMaximum_tendsto_supremum hD ω hω).pow p)

end ProphetSecretary.Analysis
