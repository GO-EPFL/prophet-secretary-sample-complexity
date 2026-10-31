import ProphetSecretary.Limiting.HybridBranchLaw
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-!
# Integration over the analytical Poisson count

The count mixture integrates the outcomes of one shared rule. Integrability of
the actual outcome proves summability of the branch expectations; it is not an
assumption about separately optimized count-aware policies.
-/

open MeasureTheory Set
open scoped BigOperators Classical ENNReal

namespace ProphetSecretary.Limiting

variable {Seed : Type*} [MeasurableSpace Seed]

lemma hasSum_worldLaw_fibers (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (f : World Seed → ℝ) (hm : Measurable f) (hf : Integrable f (worldLaw μ ν)) :
    HasSum (fun N : ℕ => poissonWeight μ.mass N *
      ∫ v, f (configurationMk N v.1, v.2) ∂(arrayLaw μ N).prod ν)
      (∫ v, f v ∂worldLaw μ ν) := by
  rw [worldLaw_eq_sum_fibers] at hf
  have hs := hasSum_integral_measure hf
  have hi (N : ℕ) :
      (∫ v, f v ∂ENNReal.ofReal (poissonWeight μ.mass N) • ((fiberLaw μ N).prod ν)) =
      poissonWeight μ.mass N * ∫ v, f (configurationMk N v.1, v.2) ∂(arrayLaw μ N).prod ν := by
    have hw : 0 ≤ poissonWeight μ.mass N := by unfold poissonWeight; positivity
    rw [integral_smul_measure, ENNReal.toReal_ofReal hw, smul_eq_mul]
    congr 1
    have hmp := world_fiber_measurePreserving μ ν N
    have h := integral_map (μ := (arrayLaw μ N).prod ν) hmp.measurable.aemeasurable hm.aestronglyMeasurable
    rw [hmp.map_eq] at h
    exact h
  convert! hs using 1
  · funext N
    exact (hi N).symm
  · rw [← worldLaw_eq_sum_fibers]

lemma integral_worldLaw_fibers (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (f : World Seed → ℝ) (hm : Measurable f) (hf : Integrable f (worldLaw μ ν)) :
    (∫ v, f v ∂worldLaw μ ν) =
      ∑' N : ℕ, poissonWeight μ.mass N * ∫ v, f (configurationMk N v.1, v.2) ∂(arrayLaw μ N).prod ν :=
  (hasSum_worldLaw_fibers μ ν f hm hf).tsum_eq.symm

end ProphetSecretary.Limiting
