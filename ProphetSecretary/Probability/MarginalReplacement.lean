import ProphetSecretary.Probability.CandidateValue

/-!
# Replacing a marginal by an independent draw

The replacement sampler changes exactly one product-law factor. Invariant
functionals of the erased coordinate therefore have the same expectation under
arbitrary changes to that marginal; this is derived from the sampler law.
-/

open MeasureTheory Set
open scoped Classical ENNReal BigOperators

namespace ProphetSecretary.Model

lemma measurePreserving_replaceCoordinate_law {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace A] (μ : ι → Measure A) [∀ j, IsProbabilityMeasure (μ j)]
    (ν : Measure A) [IsProbabilityMeasure ν] (i : ι) :
    MeasurePreserving (fun z : (ι → A) × A ↦ Function.update z.1 i z.2)
      ((Measure.pi μ).prod ν) (Measure.pi (Function.update μ i ν)) := by
  haveI : ∀ j, IsProbabilityMeasure ((Function.update μ i ν) j) := by
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using (inferInstance : IsProbabilityMeasure ν)
    · simpa only [Function.update_of_ne hj] using (inferInstance : IsProbabilityMeasure (μ j))
  have hm : Measurable (fun z : (ι → A) × A ↦ Function.update z.1 i z.2) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j = i
    · subst j
      simpa only [Function.update_self] using (measurable_snd : Measurable (Prod.snd : (ι → A) × A → A))
    · simpa only [Function.update_of_ne hj, Function.comp_def] using ((measurable_pi_apply j).comp measurable_fst)
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  have he : (fun z : (ι → A) × A ↦ Function.update z.1 i z.2) ⁻¹' (univ.pi s) =
      (univ.pi (Function.update s i univ)) ×ˢ s i := by
    ext z
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · subst j
          simp
        · simpa [Function.update_of_ne hj] using hz j
      · simpa using hz i
    · rintro ⟨hz, hi⟩ j
      by_cases hj : j = i
      · subst j
        simpa using hi
      · simpa [Function.update_of_ne hj] using hz j
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), he, Measure.prod_prod, Measure.pi_pi]
  have hleft : (∏ j, μ j ((Function.update s i univ) j)) = ∏ j ∈ Finset.univ.erase i, μ j (s j) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [Function.update_self, measure_univ, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hleft, ← Finset.prod_erase_mul _ _ (Finset.mem_univ i), Function.update_self]
  congr 1
  apply Finset.prod_congr rfl
  intro j hj
  rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]

namespace Instance

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- Only the candidate law changes; the independent clocks and auxiliary
randomness retain their original joint law. -/
lemma replaceValue_crossLaw_measurePreserving (P Q : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (hPQ : ∀ j, j ≠ i → P.law j = Q.law j) :
    MeasurePreserving (replaceValue i) ((P.worldLaw ν).prod (Q.law i)) (Q.worldLaw ν) := by
  have he : Function.update P.law i (Q.law i) = Q.law := by
    funext j
    by_cases hj : j = i
    · subst j
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne hj, hPQ j hj]
  have hs := measurePreserving_swap_last P.valuesLaw ((clocksLaw n).prod ν) (Q.law i)
  have hc := measurePreserving_replaceCoordinate_law P.law (Q.law i) i
  rw [he] at hc
  exact (hc.prod (MeasurePreserving.id ((clocksLaw n).prod ν))).comp hs

/-- An erased-coordinate functional has identical expectations when only that
marginal changes. Its invariance is a pathwise equality, not an independence
field of a policy interface. -/
lemma integral_eq_of_replaceValue_invariant (P Q : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (hPQ : ∀ j, j ≠ i → P.law j = Q.law j)
    (f : World n Seed → ℝ) (hf : Measurable f) (hInt : Integrable f (P.worldLaw ν))
    (hinv : ∀ (ω : World n Seed) (a : ℝ), f (Function.update ω.1 i a, ω.2) = f ω) :
    (∫ ω, f ω ∂P.worldLaw ν) = ∫ ω, f ω ∂Q.worldLaw ν := by
  have hrep := P.replaceValue_crossLaw_measurePreserving Q ν i hPQ
  have hm := integral_map (μ := (P.worldLaw ν).prod (Q.law i)) hrep.measurable.aemeasurable hf.aestronglyMeasurable
  rw [hrep.map_eq] at hm
  rw [hm]
  have he : (fun v : World n Seed × ℝ ↦ f (replaceValue i v)) = (fun v ↦ f v.1) := by
    funext v
    exact hinv v.1 v.2
  rw [he]
  have hAux := (measurePreserving_fst (μ := P.worldLaw ν) (ν := Q.law i)).integrable_comp_of_integrable hInt
  have hp := integral_prod (fun v : World n Seed × ℝ ↦ f v.1) hAux
  rw [hp]
  simp only [integral_const, probReal_univ, one_smul]

end Instance
end ProphetSecretary.Model
