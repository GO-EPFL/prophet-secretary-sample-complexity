import ProphetSecretary.Statistics.RestrictedTrainingState
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Splitting actual candidate and other training rows

An explicit finite index equivalence separates the candidate's complete row
from all other coordinates. The installed product-measure equivalences prove
that the resulting arrays have exactly the independent other-instance and
candidate-row laws. Reconstruction is a measurable inverse on every array.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ}

noncomputable def candidateTrainingIndexEquiv (i : Fin n) :
    ((Fin (Finset.univ.erase i).card × Fin k) ⊕ Fin k) ≃ (Fin n × Fin k) := by
  let A := (Finset.univ : Finset (Fin n)).erase i
  let f : ((Fin A.card × Fin k) ⊕ Fin k) → (Fin n × Fin k) :=
    Sum.elim (fun q => (stateEmbedding A q.1,q.2)) (fun l => (i,l))
  apply Equiv.ofBijective f
  constructor
  · intro s t heq
    cases s with
    | inl q =>
      cases t with
      | inl r =>
        exact congrArg Sum.inl (Prod.ext ((stateEmbedding A).injective
          (congrArg (fun z : Fin n × Fin k => z.1) heq)) (congrArg (fun z : Fin n × Fin k => z.2) heq))
      | inr l =>
        have hni := (Finset.mem_erase.mp (stateEmbedding_mem A q.1)).1
        exact False.elim (hni (congrArg (fun z : Fin n × Fin k => z.1) heq))
    | inr l =>
      cases t with
      | inl q =>
        have hni := (Finset.mem_erase.mp (stateEmbedding_mem A q.1)).1
        exact False.elim (hni (congrArg (fun z : Fin n × Fin k => z.1) heq).symm)
      | inr r => exact congrArg Sum.inr (congrArg (fun z : Fin n × Fin k => z.2) heq)
  · rintro ⟨j,l⟩
    by_cases hji : j=i
    · exact ⟨Sum.inr l,Prod.ext hji.symm rfl⟩
    · have hjA : j∈A := Finset.mem_erase.mpr ⟨hji,Finset.mem_univ _⟩
      exact ⟨Sum.inl (stateIndex A j hjA,l),Prod.ext (stateEmbedding_stateIndex A j hjA) rfl⟩

lemma candidateTrainingIndexEquiv_inl (i : Fin n) (q : Fin (Finset.univ.erase i).card × Fin k) :
    candidateTrainingIndexEquiv (k:=k) i (Sum.inl q) = (stateEmbedding (Finset.univ.erase i) q.1,q.2) := rfl

lemma candidateTrainingIndexEquiv_inr (i : Fin n) (l : Fin k) :
    candidateTrainingIndexEquiv (k:=k) i (Sum.inr l) = (i,l) := rfl

noncomputable def splitTrainingRowEquiv (i : Fin n) :
    ((Fin n × Fin k) → ℝ) ≃ᵐ ((((Fin (Finset.univ.erase i).card × Fin k) → ℝ)) × (Fin k → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin k => ℝ) (candidateTrainingIndexEquiv i)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

lemma splitTrainingRowEquiv_apply (i : Fin n) (a : (Fin n × Fin k) → ℝ) :
    splitTrainingRowEquiv i a =
      (restrictTrainingCoordinates (Finset.univ.erase i) a,fun l => a (i,l)) := rfl

/-- This law identity proves the independence needed when the candidate row
influences the training-selected scalar while error envelopes use other rows. -/
lemma Instance.splitTrainingRow_measurePreserving (P : Instance n) (i : Fin n) :
    MeasurePreserving (splitTrainingRowEquiv (k:=k) i) (P.trainingCoordinateLaw k)
      (((P.restrictTo (Finset.univ.erase i)).trainingCoordinateLaw k).prod (Measure.pi (fun _ : Fin k => P.law i))) := by
  let e := candidateTrainingIndexEquiv (k:=k) i
  let μ : (Fin n × Fin k) → Measure ℝ := fun q => P.law q.1
  let μ' := fun q => μ (e q)
  haveI : ∀ q, IsProbabilityMeasure (μ' q) := fun q => P.probability (e q).1
  have h1 := (measurePreserving_piCongrLeft μ e).symm
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin k => ℝ) e)
  have h2 := measurePreserving_sumPiEquivProdPi μ'
  exact h2.comp h1

/-- Adding the independent policy seed leaves the same exact product split. -/
lemma Instance.splitTrainingRow_seed_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (P : Instance n) (i : Fin n) (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (fun q : (((Fin n × Fin k) → ℝ) × Seed) =>
      ((splitTrainingRowEquiv i q.1).1,((splitTrainingRowEquiv i q.1).2,q.2)))
      ((P.trainingCoordinateLaw k).prod ν)
      (((P.restrictTo (Finset.univ.erase i)).trainingCoordinateLaw k).prod
        ((Measure.pi (fun _ : Fin k => P.law i)).prod ν)) :=
  (measurePreserving_prodAssoc _ _ ν).comp ((P.splitTrainingRow_measurePreserving i).prod (MeasurePreserving.id ν))

end ProphetSecretary.Model
