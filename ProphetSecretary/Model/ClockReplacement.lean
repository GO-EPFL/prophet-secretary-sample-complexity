import ProphetSecretary.Reach.Pending

/-!
# Replacing one clock by an independent uniform

The replacement map preserves the entire instance law. This permits integration over
a candidate's arrival time while holding its value, the other observations and the
policy seed fixed, without supplying future values to the policy.
-/

open MeasureTheory Set ProbabilityTheory
open scoped ENNReal BigOperators

namespace ProphetSecretary.Model

lemma measurePreserving_replaceCoordinate {ι A : Type*} [Fintype ι] [DecidableEq ι]
    [MeasurableSpace A] (μ : ι → Measure A) [∀ j, IsProbabilityMeasure (μ j)] (i : ι) :
    MeasurePreserving (fun z : (ι → A) × A => Function.update z.1 i z.2)
      ((Measure.pi μ).prod (μ i)) (Measure.pi μ) := by
  have hm : Measurable (fun z : (ι → A) × A => Function.update z.1 i z.2) := by
    apply measurable_pi_lambda
    intro j
    by_cases hj : j = i
    · subst j; simpa using measurable_snd
    · simpa only [Function.update_of_ne hj, Function.comp_def] using ((measurable_pi_apply j).comp measurable_fst)
  refine ⟨hm, ?_⟩
  symm
  apply Measure.pi_eq
  intro s hs
  have he : (fun z : (ι → A) × A => Function.update z.1 i z.2) ⁻¹' (univ.pi s) =
      (univ.pi (Function.update s i univ)) ×ˢ s i := by
    ext z
    simp only [mem_preimage, mem_pi, mem_univ, forall_true_left, mem_prod]
    constructor
    · intro hz
      refine ⟨?_, ?_⟩
      · intro j
        by_cases hj : j = i
        · subst j; simp
        · simpa [Function.update_of_ne hj] using hz j
      · simpa using hz i
    · rintro ⟨hz, hi⟩ j
      by_cases hj : j = i
      · subst j; simpa using hi
      · simpa [Function.update_of_ne hj] using hz j
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs), he, Measure.prod_prod, Measure.pi_pi]
  have hprod : (∏ j, μ j ((Function.update s i univ) j)) = ∏ j ∈ Finset.univ.erase i, μ j (s j) := by
    rw [← Finset.prod_erase_mul _ _ (Finset.mem_univ i)]
    simp only [Function.update_self, measure_univ, mul_one]
    apply Finset.prod_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hprod, Finset.prod_erase_mul _ _ (Finset.mem_univ i)]

/-- Interchanging two independent factors, while preserving the first one. -/
lemma measurePreserving_swap_last {A B C : Type*} [MeasurableSpace A] [MeasurableSpace B]
    [MeasurableSpace C] (μ : Measure A) (ν : Measure B) (ρ : Measure C)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] [IsProbabilityMeasure ρ] :
    MeasurePreserving (fun z : (A × B) × C => ((z.1.1, z.2), z.1.2))
      ((μ.prod ν).prod ρ) ((μ.prod ρ).prod ν) := by
  have h₁ := measurePreserving_prodAssoc μ ν ρ
  have h₂ := (MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := ν) (ν := ρ))
  have h₃ := (measurePreserving_prodAssoc μ ρ ν).symm MeasurableEquiv.prodAssoc
  exact h₃.comp (h₂.comp h₁)

namespace Instance

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

/-- Only the candidate's clock is replaced; values and the policy seed are retained. -/
def replaceClock (i : Fin n) (z : World n Seed × ℝ) : World n Seed :=
  (z.1.1, (Function.update z.1.2.1 i z.2, z.1.2.2))

lemma replaceClock_measurePreserving (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) :
    MeasurePreserving (replaceClock i) ((P.worldLaw ν).prod uniformClock) (P.worldLaw ν) := by
  have h₁ := measurePreserving_prodAssoc P.valuesLaw ((clocksLaw n).prod ν) uniformClock
  have h₂ := (MeasurePreserving.id P.valuesLaw).prod
    (measurePreserving_swap_last (clocksLaw n) ν uniformClock)
  have hclock := measurePreserving_replaceCoordinate (fun _ : Fin n => uniformClock) i
  have h₃ := (MeasurePreserving.id P.valuesLaw).prod (hclock.prod (MeasurePreserving.id ν))
  exact h₃.comp (h₂.comp h₁)

omit [MeasurableSpace Seed] in
lemma pendingTime_replaceClock (π : Policy Seed n) (i : Fin n) (z : World n Seed × ℝ) :
    π.pendingTime (replaceClock i z).2.2 (replaceClock i z).1 (replaceClock i z).2.1 i =
      π.pendingTime z.1.2.2 z.1.1 z.1.2.1 i := by
  change π.pendingTime z.1.2.2 z.1.1 (Function.update z.1.2.1 i z.2) i = _
  have h := π.pendingTime_update z.1.2.2 z.1.1 z.1.2.1 i (z.1.1 i) z.2
  simpa only [Function.update_eq_self] using h

end Instance
end ProphetSecretary.Model
