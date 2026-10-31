import ProphetSecretary.Probability.InfiniteCoordinateReplacement
import Mathlib.MeasureTheory.Measure.WithDensity

/-!
# A likelihood change in one coordinate of an infinite product

A fresh coordinate with a prescribed probability law replaces the old one.
Finite cylinders prove the resulting product law. Weighting this exact map
then identifies the full infinite-product density, without a finite-support
assumption on any marginal.
-/

open MeasureTheory Set
open scoped Classical ENNReal

namespace ProphetSecretary.Probability

lemma measurePreserving_withDensity {A B : Type*} [MeasurableSpace A] [MeasurableSpace B]
    {μ : Measure A} {ν : Measure B} {g : A → B} (hg : MeasurePreserving g μ ν)
    {f : B → ℝ≥0∞} (hf : Measurable f) :
    MeasurePreserving g (μ.withDensity (fun x => f (g x))) (ν.withDensity f) := by
  refine ⟨hg.measurable,?_⟩
  refine Measure.ext_of_lintegral _ (fun φ hφ => ?_)
  rw [lintegral_map hφ hg.measurable]
  change (∫⁻ x, (φ ∘ g) x ∂μ.withDensity (f ∘ g))=∫⁻ y, φ y ∂ν.withDensity f
  rw [lintegral_withDensity_eq_lintegral_mul μ (hf.comp hg.measurable) (hφ.comp hg.measurable),
    lintegral_withDensity_eq_lintegral_mul ν hf hφ]
  change (∫⁻ x, (f*φ) (g x) ∂μ)=∫⁻ y, (f*φ) y ∂ν
  rw [← lintegral_map (hf.mul hφ) hg.measurable,hg.map_eq]

lemma infinite_changeCoordinate_measurePreserving {ι A : Type*} [DecidableEq ι] [MeasurableSpace A]
    (μ : ι → Measure A) [∀ j, IsProbabilityMeasure (μ j)]
    (i : ι) (q : Measure A) [IsProbabilityMeasure q] :
    MeasurePreserving (fun z : (ι → A) × A => Function.update z.1 i z.2)
      ((Measure.infinitePi μ).prod q) (Measure.infinitePi (Function.update μ i q)) := by
  let μ' := Function.update μ i q
  haveI (j : ι) : IsProbabilityMeasure (μ' j) := by
    by_cases hji : j=i
    · subst j
      simpa only [μ',Function.update_self] using (inferInstance : IsProbabilityMeasure q)
    · simpa only [μ',Function.update_of_ne hji] using (inferInstance : IsProbabilityMeasure (μ j))
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
    rw [hPre,Measure.prod_prod,Measure.infinitePi_pi μ (fun j _ => ht j)]
    have hErase : (∏ j ∈ s.erase i, μ j (t j)) = ∏ j ∈ s.erase i, μ' j (t j) := by
      apply Finset.prod_congr rfl
      intro j hj
      simp only [μ',Function.update_of_ne (Finset.mem_erase.mp hj).1]
    rw [hErase]
    change (∏ j ∈ s.erase i, μ' j (t j))*q (t i)=∏ j ∈ s, μ' j (t j)
    rw [← show μ' i=q from Function.update_self i q μ]
    exact Finset.prod_erase_mul _ _ his
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
    apply Finset.prod_congr rfl
    intro j hj
    have hji : j ≠ i := fun h => his (h ▸ hj)
    simp only [Function.update_of_ne hji]

lemma infinitePi_update_withDensity {ι A : Type*} [DecidableEq ι] [MeasurableSpace A]
    (μ : ι → Measure A) [∀ j, IsProbabilityMeasure (μ j)] (i : ι)
    (f : A → ℝ≥0∞) (hf : Measurable f) [IsProbabilityMeasure ((μ i).withDensity f)] :
    Measure.infinitePi (Function.update μ i ((μ i).withDensity f))=
      (Measure.infinitePi μ).withDensity (fun x => f (x i)) := by
  have hNew := infinite_changeCoordinate_measurePreserving μ i ((μ i).withDensity f)
  have hOld := infinite_replaceCoordinate_measurePreserving μ i
  have hWeighted := measurePreserving_withDensity hOld (hf.comp (measurable_pi_apply i))
  calc
    _ = (((Measure.infinitePi μ).prod ((μ i).withDensity f)).map
        (fun z : (ι → A) × A => Function.update z.1 i z.2)) := hNew.map_eq.symm
    _ = (((Measure.infinitePi μ).prod (μ i)).withDensity (fun z => f z.2)).map
        (fun z : (ι → A) × A => Function.update z.1 i z.2) := by rw [prod_withDensity_right hf]
    _ = _ := by simpa only [Function.update_self,Function.comp_def] using hWeighted.map_eq

end ProphetSecretary.Probability
