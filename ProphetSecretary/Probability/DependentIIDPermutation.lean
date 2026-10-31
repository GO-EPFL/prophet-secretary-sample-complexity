import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Probability.HasLaw

/-!
# Permuting independent identical samples by an independent observation

A measurable permutation may depend on the entire first coordinate. Conditional
on that coordinate it preserves the identical product law of the samples.
Fubini proves the joint pushforward, so their independence is retained.
-/

open MeasureTheory Set Filter
open scoped Classical

namespace ProphetSecretary.Probability

lemma iid_reindex_measurePreserving {n : ℕ} {T : Type*} [MeasurableSpace T]
    (κ : Measure T) [IsProbabilityMeasure κ] (p : Equiv.Perm (Fin n)) :
    MeasurePreserving (fun x : Fin n → T => fun i => x (p i))
      (Measure.pi (fun _ : Fin n => κ)) (Measure.pi (fun _ : Fin n => κ)) := by
  have h := measurePreserving_piCongrLeft (α := fun _ : Fin n => T) (fun _ : Fin n => κ) p
  exact h.symm (MeasurableEquiv.piCongrLeft (fun _ : Fin n => T) p)

lemma dependent_iid_reindex_measurePreserving {Ω T : Type*} [MeasurableSpace Ω] [MeasurableSpace T]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Measure T) [IsProbabilityMeasure κ] {n : ℕ}
    (p : Ω → Equiv.Perm (Fin n)) (hp : ∀ i, Measurable (fun ω => p ω i)) :
    MeasurePreserving (fun z : Ω × (Fin n → T) => (z.1,fun i => z.2 (p z.1 i)))
      (μ.prod (Measure.pi (fun _ : Fin n => κ))) (μ.prod (Measure.pi (fun _ : Fin n => κ))) := by
  have hEval : Measurable (fun z : (Fin n → T) × Fin n => z.1 z.2) :=
    measurable_from_prod_countable_left (fun i => measurable_pi_apply i)
  have hMap : Measurable (fun z : Ω × (Fin n → T) => (z.1,fun i => z.2 (p z.1 i))) := by
    apply measurable_fst.prodMk
    apply measurable_pi_lambda
    intro i
    exact hEval.comp (measurable_snd.prodMk ((hp i).comp measurable_fst))
  refine ⟨hMap,?_⟩
  ext S hS
  rw [Measure.map_apply hMap hS,Measure.prod_apply (hS.preimage hMap),Measure.prod_apply hS]
  apply lintegral_congr_ae
  exact Eventually.of_forall (fun ω => by
    have hSection : MeasurableSet {x : Fin n → T | (ω,x)∈S} := measurable_prodMk_left hS
    have h := (iid_reindex_measurePreserving κ (p ω)).measure_preimage hSection.nullMeasurableSet
    exact h)

end ProphetSecretary.Probability
