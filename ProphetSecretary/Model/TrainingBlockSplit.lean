import ProphetSecretary.Model.TrainingCoordinates

/-!
# An independent block of an actual training reservoir

An injective choice of columns separates the empirical block from all
remaining training coordinates. The split is a measurable equivalence and
has the actual product law, conditional on any fixed instance. No ONLINE
coordinate is part of this reservoir or its remainder.
-/

open MeasureTheory Set
open scoped Classical
namespace ProphetSecretary.Model

variable {n m c : ℕ}

abbrev TrainingBlockIndex (n : ℕ) (e : Fin m ↪ Fin c) :=
  {q : Fin n × Fin c // q.2∈Set.range e}

abbrev TrainingRemainderIndex (n : ℕ) (e : Fin m ↪ Fin c) :=
  {q : Fin n × Fin c // q.2∉Set.range e}

noncomputable def trainingBlockIndexEquiv (e : Fin m ↪ Fin c) :
    (Fin n × Fin m) ≃ TrainingBlockIndex n e :=
  Equiv.ofBijective (fun q => ⟨(q.1,e q.2),⟨q.2,rfl⟩⟩) (by
    constructor
    · intro a b h
      have hVal := congrArg Subtype.val h
      have hFirst : a.1=b.1 := congrArg (fun q : Fin n × Fin c => q.1) hVal
      have hSecond : e a.2=e b.2 := congrArg (fun q : Fin n × Fin c => q.2) hVal
      exact Prod.ext hFirst (e.injective hSecond)
    · rintro ⟨q,j,hj⟩
      refine ⟨(q.1,j),?_⟩
      apply Subtype.ext
      exact Prod.ext rfl hj)

noncomputable def splitTrainingBlock (e : Fin m ↪ Fin c) :
    Reservoir n c ≃ᵐ (Reservoir n m × (TrainingRemainderIndex n e → ℝ)) :=
  (reservoirCoordinates (n:=n) (k:=c)).trans
    ((MeasurableEquiv.piEquivPiSubtypeProd (fun _ : Fin n × Fin c => ℝ)
      (fun q => q.2∈Set.range e)).trans
      (((MeasurableEquiv.piCongrLeft (fun _ : TrainingBlockIndex n e => ℝ)
        (trainingBlockIndexEquiv e)).symm.trans (reservoirCoordinates (n:=n) (k:=m)).symm).prodCongr
          (MeasurableEquiv.refl (TrainingRemainderIndex n e → ℝ))))

noncomputable def Instance.trainingRemainderLaw (P : Instance n) (e : Fin m ↪ Fin c) :
    Measure (TrainingRemainderIndex n e → ℝ) := Measure.pi (fun q => P.law q.val.1)

instance Instance.trainingRemainderLaw_probability (P : Instance n) (e : Fin m ↪ Fin c) :
    IsProbabilityMeasure (P.trainingRemainderLaw e) := by unfold Instance.trainingRemainderLaw; infer_instance

lemma splitTrainingBlock_first (e : Fin m ↪ Fin c) (y : Reservoir n c) (i : Fin n) (j : Fin m) :
    (splitTrainingBlock e y).1 i j=y i (e j) := rfl

lemma Instance.splitTrainingBlock_measurePreserving (P : Instance n) (e : Fin m ↪ Fin c) :
    MeasurePreserving (splitTrainingBlock e) (P.reservoirLaw c)
      ((P.reservoirLaw m).prod (P.trainingRemainderLaw e)) := by
  let μ := fun q : Fin n × Fin c => P.law q.1
  have hSplit := measurePreserving_piEquivPiSubtypeProd μ (fun q => q.2∈Set.range e)
  have hLeft := (measurePreserving_piCongrLeft (fun q : TrainingBlockIndex n e => P.law q.val.1)
    (trainingBlockIndexEquiv e)).symm
      (MeasurableEquiv.piCongrLeft (fun _ : TrainingBlockIndex n e => ℝ) (trainingBlockIndexEquiv e))
  exact ((P.reservoirCoordinates_symm_measurePreserving m).comp hLeft).prod
    (MeasurePreserving.id (P.trainingRemainderLaw e)) |>.comp
      (hSplit.comp (P.reservoirCoordinates_measurePreserving c))

end ProphetSecretary.Model
