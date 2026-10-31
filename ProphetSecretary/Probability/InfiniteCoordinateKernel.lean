import ProphetSecretary.Probability.InfiniteCoordinateDensity

/-!
# Independent randomization of one infinite-product coordinate

A jointly measurable transition of one coordinate and a fresh independent
auxiliary sample has the prescribed new marginal. Checking finite cylinders
proves the full product pushforward; untouched coordinates stay independent.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Probability

lemma infinite_randomCoordinate_measurePreserving {ι A U : Type*} [DecidableEq ι]
    [MeasurableSpace A] [MeasurableSpace U]
    (μ : ι → Measure A) [∀ j, IsProbabilityMeasure (μ j)] (i : ι)
    (ρ : Measure U) [IsProbabilityMeasure ρ] (q : Measure A) [IsProbabilityMeasure q]
    {F : A × U → A} (hF : MeasurePreserving F ((μ i).prod ρ) q) :
    MeasurePreserving (fun z : (ι → A) × U => Function.update z.1 i (F (z.1 i,z.2)))
      ((Measure.infinitePi μ).prod ρ) (Measure.infinitePi (Function.update μ i q)) := by
  let μ' := Function.update μ i q
  haveI (j : ι) : IsProbabilityMeasure (μ' j) := by
    by_cases hj : j=i
    · subst j
      simpa only [μ',Function.update_self] using (inferInstance : IsProbabilityMeasure q)
    · simpa only [μ',Function.update_of_ne hj] using (inferInstance : IsProbabilityMeasure (μ j))
  have hm : Measurable (fun z : (ι → A) × U => Function.update z.1 i (F (z.1 i,z.2))) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j=i
    · subst j
      simpa only [Function.update_self,Function.comp_def] using hF.measurable.comp
        (((measurable_pi_apply i).comp measurable_fst).prodMk measurable_snd)
    · simpa only [Function.update_of_ne hj,Function.comp_def] using (measurable_pi_apply j).comp measurable_fst
  refine ⟨hm,?_⟩
  apply Measure.eq_infinitePi
  intro s t ht
  have hBox : MeasurableSet (Set.pi (s : Set ι) t) := MeasurableSet.pi s.countable_toSet (fun j _ => ht j)
  rw [Measure.map_apply hm hBox]
  by_cases his : i∈s
  · have hSection (u : U) :
        (fun z : ι → A => Function.update z i (F (z i,u))) ⁻¹' Set.pi (s : Set ι) t=
          Set.pi (s : Set ι) (fun j => if j=i then (fun x => F (x,u)) ⁻¹' t i else t j) := by
      ext z
      simp only [mem_preimage,mem_pi,Finset.mem_coe]
      constructor <;> intro hz j hj <;> by_cases hji : j=i
      · subst j
        simpa only [Function.update_self,if_true,mem_preimage] using hz i hj
      · simpa only [Function.update_of_ne hji,if_neg hji] using hz j hj
      · subst j
        simpa only [Function.update_self,if_true,mem_preimage] using hz i hj
      · simpa only [Function.update_of_ne hji,if_neg hji] using hz j hj
    have hMeasSection (u : U) (j : ι) : MeasurableSet (if j=i then (fun x => F (x,u)) ⁻¹' t i else t j) := by
      by_cases hj : j=i
      · rw [if_pos hj]
        exact (ht i).preimage (hF.measurable.comp (measurable_id.prodMk measurable_const))
      · simpa only [if_neg hj] using ht j
    have hProd (u : U) :
        (Measure.infinitePi μ) ((fun z : ι → A => Function.update z i (F (z i,u))) ⁻¹' Set.pi (s : Set ι) t)=
          (∏ j∈s.erase i, μ j (t j))*μ i ((fun x => F (x,u)) ⁻¹' t i) := by
      rw [hSection u,Measure.infinitePi_pi μ (fun j _ => hMeasSection u j),← Finset.prod_erase_mul _ _ his]
      congr 1
      apply Finset.prod_congr rfl
      intro j hj
      rw [if_neg (Finset.mem_erase.mp hj).1]
      simp only [ite_true]
    have hRate : (∫⁻ u, μ i ((fun x => F (x,u)) ⁻¹' t i) ∂ρ)=q (t i) := by
      rw [← hF.map_eq,Measure.map_apply hF.measurable (ht i),Measure.prod_apply_symm ((ht i).preimage hF.measurable)]
      rfl
    rw [Measure.prod_apply_symm (hBox.preimage hm)]
    change (∫⁻ u, (Measure.infinitePi μ) ((fun z : ι → A => Function.update z i (F (z i,u))) ⁻¹' Set.pi (s : Set ι) t) ∂ρ)=_
    simp_rw [hProd]
    rw [lintegral_const_mul' _ _ (ENNReal.prod_ne_top (fun j _ => measure_ne_top (μ j) (t j))),hRate]
    have hErase : (∏ j∈s.erase i, μ j (t j))=∏ j∈s.erase i, μ' j (t j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [μ',Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [hErase]
    change (∏ j∈s.erase i, μ' j (t j))*q (t i)=∏ j∈s, μ' j (t j)
    rw [← show μ' i=q from Function.update_self i q μ]
    exact Finset.prod_erase_mul _ _ his
  · have hPre : (fun z : (ι → A) × U => Function.update z.1 i (F (z.1 i,z.2))) ⁻¹' Set.pi (s : Set ι) t=
        Set.pi (s : Set ι) t ×ˢ univ := by
      ext z
      simp only [mem_preimage,mem_pi,Finset.mem_coe,mem_prod,mem_univ,and_true]
      constructor <;> intro hz j hj
      · simpa only [Function.update_of_ne (show j≠i from fun h => his (h ▸ hj))] using hz j hj
      · simpa only [Function.update_of_ne (show j≠i from fun h => his (h ▸ hj))] using hz j hj
    rw [hPre,Measure.prod_prod,measure_univ,mul_one,Measure.infinitePi_pi μ (fun j _ => ht j)]
    apply Finset.prod_congr rfl
    intro j hj
    simp only [Function.update_of_ne (show j≠i from fun h => his (h ▸ hj))]

end ProphetSecretary.Probability
