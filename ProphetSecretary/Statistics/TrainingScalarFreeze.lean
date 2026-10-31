import ProphetSecretary.Statistics.TrainingRowSplit

/-!
# Holding the candidate row and independent policy seed fixed

The actual product-law split separates other samples from the candidate's row
and auxiliary seed. A scalar selected from all training data becomes a
measurable function of the other rows once those two inputs are fixed. The
measurable inverse reconstructs the original full array on every outcome.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Model

variable {n k : ℕ} {Seed : Type*} [MeasurableSpace Seed]

noncomputable def splitTrainingRowSeedEquiv (i : Fin n) :
    (((Fin n × Fin k) → ℝ) × Seed) ≃ᵐ
      (((Fin (Finset.univ.erase i).card × Fin k) → ℝ) × ((Fin k → ℝ) × Seed)) :=
  ((splitTrainingRowEquiv i).prodCongr (MeasurableEquiv.refl Seed)).trans MeasurableEquiv.prodAssoc

lemma splitTrainingRowSeedEquiv_apply (i : Fin n) (a : (Fin n × Fin k) → ℝ) (r : Seed) :
    splitTrainingRowSeedEquiv i (a,r) = (restrictTrainingCoordinates (Finset.univ.erase i) a,((fun l => a (i,l)),r)) := rfl

lemma Instance.splitTrainingRowSeedEquiv_measurePreserving (P : Instance n) (i : Fin n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (splitTrainingRowSeedEquiv (k:=k) (Seed:=Seed) i) ((P.trainingCoordinateLaw k).prod ν)
      (((P.restrictTo (Finset.univ.erase i)).trainingCoordinateLaw k).prod
        ((Measure.pi (fun _ : Fin k => P.law i)).prod ν)) := P.splitTrainingRow_seed_measurePreserving i ν

lemma Instance.mergeTrainingRowSeed_measurePreserving (P : Instance n) (i : Fin n)
    (ν : Measure Seed) [IsProbabilityMeasure ν] :
    MeasurePreserving (splitTrainingRowSeedEquiv (k:=k) (Seed:=Seed) i).symm
      (((P.restrictTo (Finset.univ.erase i)).trainingCoordinateLaw k).prod
        ((Measure.pi (fun _ : Fin k => P.law i)).prod ν))
      ((P.trainingCoordinateLaw k).prod ν) :=
  (P.splitTrainingRowSeedEquiv_measurePreserving i ν).symm (splitTrainingRowSeedEquiv i)

lemma restrictTrainingCoordinates_merge (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) (v : Fin k → ℝ) :
    restrictTrainingCoordinates (Finset.univ.erase i) ((splitTrainingRowEquiv i).symm (b,v)) = b := by
  have h := (splitTrainingRowEquiv i).apply_symm_apply (b,v)
  rw [splitTrainingRowEquiv_apply] at h
  exact congrArg Prod.fst h

noncomputable def frozenOtherScalar (Z : Reservoir n k × Seed → ℝ) (i : Fin n)
    (r : (Fin k → ℝ) × Seed) (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) : ℝ :=
  Z (reservoirCoordinates.symm ((splitTrainingRowEquiv i).symm (b,r.1)),r.2)

lemma measurable_frozenOtherScalar {Z : Reservoir n k × Seed → ℝ} (hZ : Measurable Z)
    (i : Fin n) (r : (Fin k → ℝ) × Seed) : Measurable (frozenOtherScalar Z i r) := by
  have hm : Measurable (fun b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ =>
      (splitTrainingRowEquiv i).symm (b,r.1)) :=
    (splitTrainingRowEquiv i).symm.measurable.comp (measurable_id.prodMk measurable_const)
  exact hZ.comp ((reservoirCoordinates.symm.measurable.comp hm).prodMk measurable_const)

lemma frozenOtherScalar_reconstruct (Z : Reservoir n k × Seed → ℝ) (i : Fin n)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) (r : (Fin k → ℝ) × Seed) :
    let p := (splitTrainingRowSeedEquiv (k:=k) (Seed:=Seed) i).symm (b,r)
    Z (reservoirCoordinates.symm p.1,p.2) = frozenOtherScalar Z i r b := rfl

omit [MeasurableSpace Seed] in
lemma frozenOtherScalar_range {Z : Reservoir n k × Seed → ℝ} {lo hi : ℝ}
    (hZ : ∀ p, Z p ∈ Icc lo hi) (i : Fin n) (r : (Fin k → ℝ) × Seed)
    (b : (Fin (Finset.univ.erase i).card × Fin k) → ℝ) : frozenOtherScalar Z i r b ∈ Icc lo hi :=
  hZ _

end ProphetSecretary.Model
