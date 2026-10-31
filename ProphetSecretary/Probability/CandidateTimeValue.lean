import ProphetSecretary.Probability.CandidateValue

/-!
# Conditioning selection on both candidate value and arrival time

The fixed-time probability integrates the executed policy after replacing its
candidate coordinates. Independent clock replacement and Fubini recover the
value-conditioned probability. This analytical conditioning supplies no extra
observations to the policy.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def Policy.selectionIndicatorAtTimeValue (π : Policy Seed n) (i : Fin n)
    (z : World n Seed × (ℝ × ℝ)) : ℝ :=
  if π.ActualSelects z.1.2.2 Finset.univ (Function.update z.1.1 i z.2.2)
      (Function.update z.1.2.1 i z.2.1) i then 1 else 0

lemma Policy.measurable_selectionIndicatorAtTimeValue (π : Policy Seed n)
    (hπ : π.IsMeasurable) (i : Fin n) : Measurable (π.selectionIndicatorAtTimeValue i) := by
  exact Measurable.ite (π.measurableSet_actualSelects hπ (by fun_prop)
    (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i) measurable_const measurable_const

noncomputable def Policy.selectionProbabilityAtTimeValue (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) (i : Fin n) (t a : ℝ) : ℝ :=
  ∫ ω, π.selectionIndicatorAtTimeValue i (ω, (t,a)) ∂P.worldLaw ν

lemma Policy.measurable_selectionProbabilityAtTimeValue (π : Policy Seed n)
    (hπ : π.IsMeasurable) (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Measurable (fun z : ℝ × ℝ => π.selectionProbabilityAtTimeValue P ν i z.1 z.2) :=
  (π.measurable_selectionIndicatorAtTimeValue hπ i).stronglyMeasurable.integral_prod_left'.measurable

lemma Policy.selectionProbabilityAtTimeValue_nonnegative (π : Policy Seed n)
    (P : Instance n) (ν : Measure Seed) (i : Fin n) (t a : ℝ) :
    0 ≤ π.selectionProbabilityAtTimeValue P ν i t a := by
  apply integral_nonneg
  intro ω
  change (0 : ℝ) ≤ if _ then 1 else 0
  split_ifs <;> norm_num

/-- Fixing a candidate clock leaves distinct clocks almost surely, for each
fixed real time. This uses the no-atom law of every other clock. -/
lemma Instance.world_updated_clocks_distinct_ae (P : Instance n) (ν : Measure Seed)
    [IsProbabilityMeasure ν] (i : Fin n) (t : ℝ) :
    ∀ᵐ ω : World n Seed ∂P.worldLaw ν, Function.Injective (Function.update ω.2.1 i t) := by
  have hn : ∀ᵐ ω : World n Seed ∂P.worldLaw ν, ∀ j, ω.2.1 j ≠ t :=
    ae_all_iff.mpr fun j => (P.world_clock_measurePreserving ν j).quasiMeasurePreserving.ae
      (Instance.uniformClock.ae_ne t)
  filter_upwards [P.world_clocks_distinct ν, hn] with ω hu hne
  intro j k heq
  by_cases hj : j = i
  · subst j
    by_cases hk : k = i
    · exact hk.symm
    · have hkt : t = ω.2.1 k := by simpa only [Function.update_self, Function.update_of_ne hk] using heq
      exact False.elim (hne k hkt.symm)
  · by_cases hk : k = i
    · subst k
      have hjt : ω.2.1 j = t := by simpa only [Function.update_self, Function.update_of_ne hj] using heq
      exact False.elim (hne j hjt)
    · apply hu
      simpa only [Function.update_of_ne hj, Function.update_of_ne hk] using heq

/-- Conditioning on the actual uniform arrival time, not on a newly supplied
random input available to the policy. -/
theorem Policy.selectionProbabilityAtValue_eq_timeIntegral (π : Policy Seed n)
    (hπ : π.IsMeasurable) (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (i : Fin n) (a : ℝ) :
    π.selectionProbabilityAtValue P ν i a =
      ∫ t, π.selectionProbabilityAtTimeValue P ν i t a ∂Instance.uniformClock := by
  let F : World n Seed → ℝ := fun ω => π.selectionIndicatorAtValue i (ω,a)
  have hm : Measurable F := (π.measurable_selectionIndicatorAtValue hπ i).comp
    (measurable_id.prodMk measurable_const)
  have hI : Integrable F (P.worldLaw ν) := by
    apply Integrable.of_bound hm.aestronglyMeasurable 1
    exact Eventually.of_forall fun ω => by
      change ‖if _ then (1 : ℝ) else 0‖ ≤ 1
      split_ifs <;> norm_num
  have hp := P.replaceClock_measurePreserving ν i
  have he := integral_map (μ := (P.worldLaw ν).prod Instance.uniformClock)
    hp.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hp.map_eq] at he
  change (∫ ω, F ω ∂P.worldLaw ν) = _
  rw [he]
  exact integral_prod_symm (fun z : World n Seed × ℝ => F (Instance.replaceClock i z))
    (hp.integrable_comp_of_integrable hI)

end ProphetSecretary.Model
