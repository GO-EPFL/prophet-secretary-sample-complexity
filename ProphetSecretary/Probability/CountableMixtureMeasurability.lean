import Mathlib.MeasureTheory.MeasurableSpace.Prod

/-!
# Measurability on countable disjoint mixtures

Branchwise measurable functions on a countable coproduct remain measurable
when an arbitrary independent auxiliary parameter is adjoined. The coproduct
index describes the probability space, rather than information for a policy.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Probability

variable {ι : Type*} {A : ι → Type*} [∀ i, MeasurableSpace (A i)]

lemma measurable_sigma_mk (i : ι) : Measurable (Sigma.mk i : A i → Sigma A) :=
  Measurable.of_le_map (iInf_le _ i)

lemma measurableEmbedding_sigma_mk (i : ι) : MeasurableEmbedding (Sigma.mk i : A i → Sigma A) := by
  have hInj : Function.Injective (Sigma.mk i : A i → Sigma A) := fun _ _ h => sigma_mk_injective h
  refine ⟨hInj,measurable_sigma_mk i,?_⟩
  intro S hS
  change MeasurableSet[⨅ j, (inferInstance : MeasurableSpace (A j)).map (Sigma.mk j)] ((Sigma.mk i) '' S)
  rw [MeasurableSpace.measurableSet_iInf]
  intro j
  change MeasurableSet ((Sigma.mk j) ⁻¹' ((Sigma.mk i) '' S))
  by_cases hji : j=i
  · subst j
    simpa only [hInj.preimage_image] using hS
  · have he : (Sigma.mk j) ⁻¹' ((Sigma.mk i) '' S)=∅ := by
      ext x
      constructor
      · rintro ⟨y,_,hy⟩
        exact False.elim (hji (congrArg Sigma.fst hy).symm)
      · intro h
        exact False.elim h
    rw [he]
    exact MeasurableSet.empty

lemma measurable_of_sigma_branches {B : Type*} [MeasurableSpace B] (f : Sigma A → B)
    (hf : ∀ i, Measurable (fun x : A i => f ⟨i,x⟩)) : Measurable f := by
  intro S hS
  change MeasurableSet[⨅ i, (inferInstance : MeasurableSpace (A i)).map (Sigma.mk i)] (f ⁻¹' S)
  rw [MeasurableSpace.measurableSet_iInf]
  exact fun i => hf i hS

lemma measurable_of_sigma_prod_branches [Countable ι] {Seed B : Type*}
    [MeasurableSpace Seed] [MeasurableSpace B] (f : (Sigma A) × Seed → B)
    (hf : ∀ i, Measurable (fun z : A i × Seed => f (⟨i,z.1⟩,z.2))) : Measurable f := by
  intro S hS
  have he : f ⁻¹' S=⋃ i : ι, (Prod.map (Sigma.mk i) id) ''
      ((fun z : A i × Seed => f (⟨i,z.1⟩,z.2)) ⁻¹' S) := by
    ext z
    constructor
    · intro hz
      rcases z with ⟨⟨i,x⟩,r⟩
      exact mem_iUnion.mpr ⟨i,⟨(x,r),hz,rfl⟩⟩
    · intro hz
      obtain ⟨i,z,hz,he⟩ := mem_iUnion.mp hz
      exact he ▸ hz
  rw [he]
  exact MeasurableSet.iUnion (fun i =>
    ((measurableEmbedding_sigma_mk i).prodMap MeasurableEmbedding.id).measurableSet_image' (hf i hS))

end ProphetSecretary.Probability
