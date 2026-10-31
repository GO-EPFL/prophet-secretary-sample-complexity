import ProphetSecretary.Probability.InfiniteErasure

/-!
# Resampling one coordinate of an infinite independent product

Replacing a coordinate by a fresh sample with its original marginal preserves
the complete product law. The proof checks actual finite cylinder measures,
so no finite-support or finite-index assumption is imposed.
-/
open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Probability

lemma infinite_replaceCoordinate_measurePreserving {ι A : Type*} [DecidableEq ι] [MeasurableSpace A]
    (μ : ι → Measure A) [∀ j, IsProbabilityMeasure (μ j)] (i : ι) :
    MeasurePreserving (fun z : (ι → A) × A => Function.update z.1 i z.2)
      ((Measure.infinitePi μ).prod (μ i)) (Measure.infinitePi μ) := by
  have hm : Measurable (fun z : (ι → A) × A => Function.update z.1 i z.2) := by
    apply measurable_pi_lambda
    intro j
    by_cases hji : j=i
    · subst j
      simpa only [Function.update_self] using (measurable_snd : Measurable (fun z : (ι → A) × A => z.2))
    · simpa only [Function.update_of_ne hji,Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
  refine ⟨hm,?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  have hBox : MeasurableSet (Set.pi (s : Set ι) t) := MeasurableSet.pi s.countable_toSet (fun j _ => ht j)
  rw [Measure.map_apply hm hBox]
  by_cases his : i ∈ s
  · have hPre : (fun z : (ι → A) × A => Function.update z.1 i z.2) ⁻¹' Set.pi (s : Set ι) t =
        Set.pi (↑(s.erase i) : Set ι) t ×ˢ t i := by
      ext z
      simp only [mem_preimage,mem_pi,Finset.mem_coe,mem_prod,Finset.mem_erase]
      constructor
      · intro hz
        refine ⟨?_,by simpa only [Function.update_self] using hz i his⟩
        intro j hj
        simpa only [Function.update_of_ne hj.1] using hz j hj.2
      · rintro ⟨hz,hi⟩ j hj
        by_cases hji : j=i
        · subst j
          simpa only [Function.update_self] using hi
        · simpa only [Function.update_of_ne hji] using hz j ⟨hji,hj⟩
    rw [hPre,Measure.prod_prod,Measure.infinitePi_pi μ (fun j _ => ht j),
      Finset.prod_erase_mul _ _ his]
  · have hPre : (fun z : (ι → A) × A => Function.update z.1 i z.2) ⁻¹' Set.pi (s : Set ι) t =
        Set.pi (s : Set ι) t ×ˢ univ := by
      ext z
      simp only [mem_preimage,mem_pi,Finset.mem_coe,mem_prod,mem_univ,and_true]
      constructor
      · intro hz j hj
        have hji : j ≠ i := fun h => his (h ▸ hj)
        simpa only [Function.update_of_ne hji] using hz j hj
      · intro hz j hj
        have hji : j ≠ i := fun h => his (h ▸ hj)
        simpa only [Function.update_of_ne hji] using hz j hj
    rw [hPre,Measure.prod_prod,measure_univ,mul_one,Measure.infinitePi_pi μ (fun j _ => ht j)]

end ProphetSecretary.Probability
