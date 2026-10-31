import ProphetSecretary.Limiting.CountableObservations
import Mathlib.Probability.HasLaw

/-!
# Actual finite-prefix laws and observations

Projection of the constructed countable independent values and clocks has the
finite product law. The strict history projection preserves the identities and
times of zero-valued arrivals as well.
-/

open MeasureTheory ProbabilityTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable (B : CountableInstance)

lemma prefixValues_measurePreserving (N : ℕ) :
    MeasurePreserving (fun x : ℕ → ℝ => fun i : Fin N => x i.val)
      B.individualValuesLaw (B.individualPrefix N).valuesLaw := by
  refine ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply i.val),?_⟩
  have hind := B.individualValues_independent.precomp (g := fun i : Fin N => i.val) Fin.val_injective
  have hlaw := hind.hasLaw_pi (fun i : Fin N => (B.individualValue_measurePreserving i.val).hasLaw)
  exact hlaw.map_eq

lemma prefixClocks_measurePreserving (N : ℕ) :
    MeasurePreserving (fun u : ℕ → ℝ => fun i : Fin N => u i.val)
      individualClocksLaw (Model.Instance.clocksLaw N) := by
  refine ⟨measurable_pi_lambda _ (fun i => measurable_pi_apply i.val),?_⟩
  have hind := individualClocks_independent.precomp (g := fun i : Fin N => i.val) Fin.val_injective
  have hlaw := hind.hasLaw_pi (fun i : Fin N => (individualClock_measurePreserving i.val).hasLaw)
  exact hlaw.map_eq

lemma prefixWorld_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (ν : Measure Seed) [IsProbabilityMeasure ν] (N : ℕ) :
    MeasurePreserving (fun v : (ℕ → ℝ) × ((ℕ → ℝ) × Seed) =>
      ((fun i : Fin N => v.1 i.val),((fun i : Fin N => v.2.1 i.val),v.2.2)))
      (B.individualWorldLaw ν) ((B.individualPrefix N).worldLaw ν) :=
  (B.prefixValues_measurePreserving N).prod ((prefixClocks_measurePreserving N).prod (MeasurePreserving.id ν))

noncomputable def prefixHistory (N : ℕ) (H : IndividualHistory) : Model.History N :=
  fun i => H i.val

lemma measurable_prefixHistory (N : ℕ) : Measurable (prefixHistory N) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply i.val)

lemma prefixHistory_actual (N : ℕ) (x u : ℕ → ℝ) (t : ℝ) :
    prefixHistory N (individualHistory x u t) =
      Model.history Finset.univ (fun i : Fin N => x i.val) (fun i : Fin N => u i.val) t := by
  funext i
  simp only [prefixHistory,individualHistory,Model.history,Finset.mem_univ,true_and]

end ProphetSecretary.Limiting.CountableInstance
