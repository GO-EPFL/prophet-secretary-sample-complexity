import ProphetSecretary.Model.ClockReplacement
import ProphetSecretary.Reach.FiniteReach
import Mathlib.MeasureTheory.Integral.Prod

/-!
# Integrating a candidate's fixed-value selection probability

Candidate conditioning here is an analytical value replacement. The policy remains
fixed from its design instance, and receives only its executed online history.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators Classical

namespace ProphetSecretary.Model

variable {n : ℕ} {Seed : Type*} [MeasurableSpace Seed]

namespace Instance

def replaceValue (i : Fin n) (v : World n Seed × ℝ) : World n Seed :=
  (Function.update v.1.1 i v.2, v.1.2)

lemma replaceValue_measurePreserving (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    MeasurePreserving (replaceValue i) ((P.worldLaw ν).prod (P.law i)) (P.worldLaw ν) := by
  have hs := measurePreserving_swap_last P.valuesLaw ((clocksLaw n).prod ν) (P.law i)
  have hc := measurePreserving_replaceCoordinate P.law i
  exact (hc.prod (MeasurePreserving.id ((clocksLaw n).prod ν))).comp hs

end Instance

noncomputable def Policy.selectionIndicatorAtValue (π : Policy Seed n) (i : Fin n)
    (v : World n Seed × ℝ) : ℝ :=
  if π.ActualSelects v.1.2.2 Finset.univ (Function.update v.1.1 i v.2) v.1.2.1 i then 1 else 0

lemma Policy.measurable_selectionIndicatorAtValue (π : Policy Seed n) (hπ : π.IsMeasurable) (i : Fin n) :
    Measurable (π.selectionIndicatorAtValue i) := by
  apply Measurable.ite (π.measurableSet_actualSelects hπ (by fun_prop)
    (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i) measurable_const measurable_const

lemma Policy.integrable_selectionIndicatorAtValue (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Integrable (π.selectionIndicatorAtValue i) ((P.worldLaw ν).prod (P.law i)) := by
  apply Integrable.of_bound (π.measurable_selectionIndicatorAtValue hπ i).aestronglyMeasurable 1
  exact Filter.Eventually.of_forall fun v => by unfold Policy.selectionIndicatorAtValue; split_ifs <;> norm_num

noncomputable def Policy.selectionProbabilityAtValue (π : Policy Seed n) (P : Instance n)
    (ν : Measure Seed) (i : Fin n) (a : ℝ) : ℝ :=
  ∫ ω, π.selectionIndicatorAtValue i (ω, a) ∂P.worldLaw ν

lemma Policy.measurable_selectionProbabilityAtValue (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Measurable (π.selectionProbabilityAtValue P ν i) :=
  (π.measurable_selectionIndicatorAtValue hπ i).stronglyMeasurable.integral_prod_left'.measurable

lemma Policy.integrable_selectionProbabilityAtValue (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    Integrable (π.selectionProbabilityAtValue P ν i) (P.law i) :=
  (π.integrable_selectionIndicatorAtValue hπ P ν i).integral_prod_right

lemma Policy.integral_selectionProbabilityAtValue (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] (i : Fin n) :
    (∫ a, π.selectionProbabilityAtValue P ν i a ∂P.law i) = π.selectionProbability P ν i := by
  unfold Policy.selectionProbabilityAtValue
  rw [← integral_prod_symm _ (π.integrable_selectionIndicatorAtValue hπ P ν i)]
  let f : World n Seed → ℝ := fun ω => if π.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i then 1 else 0
  have hm : Measurable f := Measurable.ite (π.measurableSet_actualSelects hπ (by fun_prop)
    (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i) measurable_const measurable_const
  have hrep := P.replaceValue_measurePreserving ν i
  have he := integral_map (μ := (P.worldLaw ν).prod (P.law i)) hrep.measurable.aemeasurable hm.aestronglyMeasurable
  rw [hrep.map_eq] at he
  calc
    _ = ∫ ω, f ω ∂P.worldLaw ν := he.symm
    _ = _ := by
      simpa only [f, Policy.selectionProbability, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
        (integral_indicator_one (μ := P.worldLaw ν) (π.measurableSet_actualSelects hπ (by fun_prop)
          (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i))

lemma Policy.selectionProbability_sum_le_one (π : Policy Seed n) (hπ : π.IsMeasurable)
    (P : Instance n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    (∑ i, π.selectionProbability P ν i) ≤ 1 := by
  let f := fun (i : Fin n) (ω : World n Seed) => if π.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i then (1 : ℝ) else 0
  have hm (i : Fin n) : Measurable (f i) := Measurable.ite (π.measurableSet_actualSelects hπ (by fun_prop)
    (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i) measurable_const measurable_const
  have hi (i : Fin n) : Integrable (f i) (P.worldLaw ν) := Integrable.of_bound (hm i).aestronglyMeasurable 1
    (Filter.Eventually.of_forall fun ω => by dsimp [f]; split_ifs <;> norm_num)
  have hpoint (ω : World n Seed) : (∑ i, f i ω) ≤ 1 := by
    by_cases hex : ∃ i, π.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i
    · obtain ⟨i, his⟩ := hex
      rw [Finset.sum_eq_single i]
      · simp [f, his]
      · intro j _ hji
        exact if_neg (fun hj => hji (π.actualSelects_unique _ _ _ _ hj his))
      · intro hn; exact False.elim (hn (Finset.mem_univ i))
    · have hn : ∀ i, ¬π.ActualSelects ω.2.2 Finset.univ ω.1 ω.2.1 i := fun i h => hex ⟨i, h⟩
      simp [f, hn]
  have hsum := integral_mono (integrable_finsetSum _ (fun i _ => hi i)) (integrable_const (1 : ℝ)) hpoint
  rw [integral_finsetSum _ (fun i _ => hi i)] at hsum
  simp only [integral_const, probReal_univ, one_smul] at hsum
  have he (i : Fin n) : (∫ ω, f i ω ∂P.worldLaw ν) = π.selectionProbability P ν i := by
    simpa only [f, Policy.selectionProbability, Set.indicator_apply, Set.mem_setOf_eq, Pi.one_apply] using
      (integral_indicator_one (μ := P.worldLaw ν) (π.measurableSet_actualSelects hπ (by fun_prop)
        (fun j => by fun_prop) (fun j => by fun_prop) Finset.univ i))
  simpa only [he] using hsum

end ProphetSecretary.Model
