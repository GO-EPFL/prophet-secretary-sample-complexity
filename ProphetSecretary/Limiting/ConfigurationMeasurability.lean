import ProphetSecretary.Limiting.FiniteIntensityPoisson
import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Measurability across actual finite configurations

The countable disjoint union of finite arrays admits measurable branchwise
constructions, including products with an arbitrary independent seed space.
This supplies mathematical measurability without making the count observable.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting

lemma configurationMk_injective (N : ℕ) : Function.Injective (configurationMk N) := by
  intro v w h
  exact sigma_mk_injective h

lemma measurableEmbedding_configurationMk (N : ℕ) : MeasurableEmbedding (configurationMk N) := by
  refine ⟨configurationMk_injective N, measurable_configuration_mk N, ?_⟩
  intro S hS
  change MeasurableSet[⨅ M : ℕ, (inferInstance : MeasurableSpace (Fin M → Point)).map (configurationMk M)]
    ((configurationMk N) '' S)
  rw [MeasurableSpace.measurableSet_iInf]
  intro M
  change MeasurableSet ((configurationMk M) ⁻¹' ((configurationMk N) '' S))
  by_cases hMN : M = N
  · subst M
    simpa only [(configurationMk_injective N).preimage_image] using hS
  · have he : (configurationMk M) ⁻¹' ((configurationMk N) '' S) = ∅ := by
      ext v
      constructor
      · intro hv
        obtain ⟨w, _hw, hEq⟩ := hv
        have hcount : N = M := congrArg (fun ω : Configuration => ω.1) hEq
        exact False.elim (hMN hcount.symm)
      · intro hv
        exact False.elim hv
    rw [he]
    exact MeasurableSet.empty

lemma measurable_of_configuration_prod_branches {Seed β : Type*}
    [MeasurableSpace Seed] [MeasurableSpace β] (f : World Seed → β)
    (hf : ∀ N, Measurable (fun v : (Fin N → Point) × Seed => f (configurationMk N v.1, v.2))) :
    Measurable f := by
  intro S hS
  have he : f ⁻¹' S = ⋃ N : ℕ,
      (Prod.map (configurationMk N) id) ''
        ((fun v : (Fin N → Point) × Seed => f (configurationMk N v.1, v.2)) ⁻¹' S) := by
    ext ω
    constructor
    · intro hω
      rcases ω with ⟨⟨N, v⟩, r⟩
      exact Set.mem_iUnion.mpr ⟨N, ⟨(v, r), hω, rfl⟩⟩
    · intro hω
      obtain ⟨N, v, hv, he⟩ := Set.mem_iUnion.mp hω
      exact he ▸ hv
  rw [he]
  apply MeasurableSet.iUnion
  intro N
  exact ((measurableEmbedding_configurationMk N).prodMap MeasurableEmbedding.id).measurableSet_image' (hf N hS)

end ProphetSecretary.Limiting
