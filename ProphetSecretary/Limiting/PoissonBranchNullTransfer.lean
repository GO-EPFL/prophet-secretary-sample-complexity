import ProphetSecretary.Limiting.HybridMixture
import ProphetSecretary.Limiting.HybridClockNullSets

/-!
# Extracting actual fixed-count null statements

Every finite count has positive probability at a positive Poisson rate. A
unit-rate construction with the same normalized marks therefore transfers
clock regularity to every analytical array branch, including when the original
intensity is zero. No realized count is supplied to a stopping callback.
-/
open MeasureTheory Set Filter
open scoped Classical NNReal ENNReal
namespace ProphetSecretary.Limiting
variable {Aux : Type*} [MeasurableSpace Aux]

lemma ae_array_of_ae_world_of_mass_pos (μ : FiniteMeasure ℝ) (ν : Measure Aux)
    [IsProbabilityMeasure ν] (hMass : 0<μ.mass) (p : Configuration × Aux → Prop)
    (h : ∀ᵐ q ∂worldLaw μ ν, p q) (N : ℕ) :
    ∀ᵐ q ∂(arrayLaw μ N).prod ν, p (configurationMk N q.1,q.2) := by
  rw [worldLaw_eq_sum_fibers,Measure.ae_sum_iff] at h
  have hp : 0<poissonWeight μ.mass N := by
    unfold poissonWeight
    have hR : (0:ℝ)<(μ.mass:ℝ) := by exact_mod_cast hMass
    positivity
  have hBase : ∀ᵐ q ∂(fiberLaw μ N).prod ν, p q :=
    (Measure.ae_ennreal_smul_measure_iff (ne_of_gt (ENNReal.ofReal_pos.mpr hp))).mp (h N)
  exact (world_fiber_measurePreserving μ ν N).quasiMeasurePreserving.ae hBase

lemma arrayLaw_normalizedIntensity (μ : FiniteMeasure ℝ) (N : ℕ) :
    arrayLaw μ.normalize.toFiniteMeasure N=arrayLaw μ N := by
  unfold arrayLaw pointLaw
  rw [ProbabilityMeasure.toFiniteMeasure_normalize_eq_self]

lemma hybridArray_combined_clocks_regular {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]
    (P : Model.Instance n) (μ : FiniteMeasure ℝ) (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) :
    ∀ᵐ q ∂(arrayLaw μ N).prod (P.worldLaw ν),
      Function.Injective (combinedClocks q.2.2.1 q.1) ∧
        ∀ i, combinedClocks q.2.2.1 q.1 i ∈ Ioo (0:ℝ) 1 := by
  have hMass : 0<μ.normalize.toFiniteMeasure.mass := by rw [ProbabilityMeasure.mass_toFiniteMeasure]; norm_num
  have h := ae_array_of_ae_world_of_mass_pos μ.normalize.toFiniteMeasure (P.worldLaw ν) hMass
    (fun v : HybridWorld n Seed => Function.Injective (combinedClocks v.2.2.1 v.1.2) ∧
      ∀ i, combinedClocks v.2.2.1 v.1.2 i ∈ Ioo (0:ℝ) 1)
    (hybrid_combined_clocks_regular P μ.normalize.toFiniteMeasure ν) N
  simpa only [arrayLaw_normalizedIntensity,configurationMk] using h
end ProphetSecretary.Limiting
