import ProphetSecretary.Analysis.MultilevelTreeIndependence

/-!
# Independent primitive coordinates at a multilevel node

A primitive coordinate is a base seed, a paired seed, or one of the paired
recursive trees. Finite product regrouping identifies their independent law
with the four-array node law already used by the estimator.
-/

open MeasureTheory

namespace ProphetSecretary.Analysis

abbrev MultilevelPairIndex (r : ℕ) := (l : Fin r) × Fin (4 ^ (r - l.val))

abbrev MultilevelPrimitiveIndex (r : ℕ) :=
  Fin (4 ^ (r + 1)) ⊕ (MultilevelPairIndex r ⊕ (MultilevelPairIndex r ⊕ MultilevelPairIndex r))

abbrev MultilevelPrimitiveType (Seed : Type*) (r : ℕ) : MultilevelPrimitiveIndex r → Type _
  | .inl _ => Seed
  | .inr (.inl _) => Seed
  | .inr (.inr (.inl q)) => MultilevelTree Seed (q.1.val + 1)
  | .inr (.inr (.inr q)) => MultilevelTree Seed q.1.val

instance {Seed : Type*} [MeasurableSpace Seed] (r : ℕ) (i : MultilevelPrimitiveIndex r) :
    MeasurableSpace (MultilevelPrimitiveType Seed r i) := by
  rcases i with b | (p | (u | l)) <;>
    dsimp only [MultilevelPrimitiveType] <;> infer_instance

noncomputable abbrev multilevelPrimitiveMeasure {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) (r : ℕ) :
    (i : MultilevelPrimitiveIndex r) → Measure (MultilevelPrimitiveType Seed r i)
  | .inl _ => μ
  | .inr (.inl _) => μ
  | .inr (.inr (.inl q)) => multilevelTreeLaw μ (q.1.val + 1)
  | .inr (.inr (.inr q)) => multilevelTreeLaw μ q.1.val

instance multilevelPrimitiveMeasure_probability {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) (i : MultilevelPrimitiveIndex r) :
    IsProbabilityMeasure (multilevelPrimitiveMeasure μ r i) := by
  rcases i with b | (p | (u | l))
  · exact (inferInstance : IsProbabilityMeasure μ)
  · exact (inferInstance : IsProbabilityMeasure μ)
  · exact multilevelTreeLaw_probability μ (u.1.val + 1)
  · exact multilevelTreeLaw_probability μ l.1.val

abbrev MultilevelFlatNodeData (Seed : Type*) (r : ℕ) :=
  (Fin (4 ^ (r + 1)) → Seed) ×
    ((MultilevelPairIndex r → Seed) ×
      (((q : MultilevelPairIndex r) → MultilevelTree Seed (q.1.val + 1)) ×
        ((q : MultilevelPairIndex r) → MultilevelTree Seed q.1.val)))

def multilevelPrimitiveToFlatEquiv (Seed : Type*) [MeasurableSpace Seed] (r : ℕ) :
    ((i : MultilevelPrimitiveIndex r) → MultilevelPrimitiveType Seed r i) ≃ᵐ
      MultilevelFlatNodeData Seed r := by
  let e₁ := MeasurableEquiv.sumPiEquivProdPi (MultilevelPrimitiveType Seed r)
  let e₂ := MeasurableEquiv.sumPiEquivProdPi
    (fun i : MultilevelPairIndex r ⊕ (MultilevelPairIndex r ⊕ MultilevelPairIndex r) =>
      MultilevelPrimitiveType Seed r (.inr i))
  let e₃ := MeasurableEquiv.sumPiEquivProdPi
    (fun i : MultilevelPairIndex r ⊕ MultilevelPairIndex r =>
      MultilevelPrimitiveType Seed r (.inr (.inr i)))
  exact e₁.trans ((MeasurableEquiv.refl _).prodCongr
    (e₂.trans ((MeasurableEquiv.refl _).prodCongr e₃)))

def multilevelFlatToNodeEquiv (Seed : Type*) [MeasurableSpace Seed] (r : ℕ) :
    MultilevelFlatNodeData Seed r ≃ᵐ MultilevelNodeData Seed r :=
  (MeasurableEquiv.refl _).prodCongr
    ((MeasurableEquiv.piCurry (fun (l : Fin r) (_ : Fin (4 ^ (r - l.val))) => Seed)).prodCongr
      ((MeasurableEquiv.piCurry (fun (l : Fin r) (_ : Fin (4 ^ (r - l.val))) =>
        MultilevelTree Seed (l.val + 1))).prodCongr
        (MeasurableEquiv.piCurry (fun (l : Fin r) (_ : Fin (4 ^ (r - l.val))) =>
          MultilevelTree Seed l.val))))

def multilevelPrimitiveToNodeEquiv (Seed : Type*) [MeasurableSpace Seed] (r : ℕ) :
    ((i : MultilevelPrimitiveIndex r) → MultilevelPrimitiveType Seed r i) ≃ᵐ
      MultilevelNodeData Seed r :=
  (multilevelPrimitiveToFlatEquiv Seed r).trans (multilevelFlatToNodeEquiv Seed r)

noncomputable def multilevelFlatNodeLaw {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) (r : ℕ) : Measure (MultilevelFlatNodeData Seed r) :=
  (Measure.pi (fun _ : Fin (4 ^ (r + 1)) => μ)).prod
    ((Measure.pi (fun _ : MultilevelPairIndex r => μ)).prod
      ((Measure.pi (fun q : MultilevelPairIndex r => multilevelTreeLaw μ (q.1.val + 1))).prod
        (Measure.pi (fun q : MultilevelPairIndex r => multilevelTreeLaw μ q.1.val))))

theorem multilevelPrimitiveToFlat_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (multilevelPrimitiveToFlatEquiv Seed r)
      (Measure.pi (multilevelPrimitiveMeasure μ r)) (multilevelFlatNodeLaw μ r) := by
  have h₁ := measurePreserving_sumPiEquivProdPi (multilevelPrimitiveMeasure μ r)
  have h₂ := measurePreserving_sumPiEquivProdPi
    (fun i : MultilevelPairIndex r ⊕ (MultilevelPairIndex r ⊕ MultilevelPairIndex r) =>
      multilevelPrimitiveMeasure μ r (.inr i))
  have h₃ := measurePreserving_sumPiEquivProdPi
    (fun i : MultilevelPairIndex r ⊕ MultilevelPairIndex r =>
      multilevelPrimitiveMeasure μ r (.inr (.inr i)))
  have ht := ((MeasurePreserving.id (Measure.pi (fun _ : MultilevelPairIndex r => μ))).prod h₃).comp h₂
  exact ((MeasurePreserving.id (Measure.pi (fun _ : Fin (4 ^ (r + 1)) => μ))).prod ht).comp h₁

theorem multilevelFlatToNode_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (multilevelFlatToNodeEquiv Seed r)
      (multilevelFlatNodeLaw μ r) (multilevelNodeLaw μ r) := by
  have ht := measurePreserving_finitePiCurry
    (fun (l : Fin r) (_ : Fin (4 ^ (r - l.val))) => μ)
  have hu := measurePreserving_finitePiCurry
    (fun (l : Fin r) (_ : Fin (4 ^ (r - l.val))) => multilevelTreeLaw μ (l.val + 1))
  have hl := measurePreserving_finitePiCurry
    (fun (l : Fin r) (_ : Fin (4 ^ (r - l.val))) => multilevelTreeLaw μ l.val)
  exact (MeasurePreserving.id (Measure.pi (fun _ : Fin (4 ^ (r + 1)) => μ))).prod
    (ht.prod (hu.prod hl))

theorem multilevelPrimitiveToNode_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving (multilevelPrimitiveToNodeEquiv Seed r)
      (Measure.pi (multilevelPrimitiveMeasure μ r)) (multilevelNodeLaw μ r) :=
  (multilevelFlatToNode_measurePreserving μ r).comp
    (multilevelPrimitiveToFlat_measurePreserving μ r)

/-- The independent primitive product is the exact image of the actual
finite random tree, not an assumed independence interface. -/
theorem multilevelTreeToPrimitive_measurePreserving {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) :
    MeasurePreserving
      ((multilevelPrimitiveToNodeEquiv Seed r).symm ∘ multilevelNodeMeasurableEquiv Seed r)
      (multilevelTreeLaw μ (r + 1)) (Measure.pi (multilevelPrimitiveMeasure μ r)) :=
  (MeasurePreserving.symm (multilevelPrimitiveToNodeEquiv Seed r)
    (multilevelPrimitiveToNode_measurePreserving μ r)).comp
      (multilevelNode_measurePreserving μ r)

def multilevelPrimitiveCoordinates (Seed : Type*) [MeasurableSpace Seed] (r : ℕ)
    (t : MultilevelTree Seed (r + 1)) :
    (i : MultilevelPrimitiveIndex r) → MultilevelPrimitiveType Seed r i :=
  (multilevelPrimitiveToNodeEquiv Seed r).symm (multilevelNodeMeasurableEquiv Seed r t)

/-- All node primitives are independent under the actual finite-tree law. -/
theorem multilevelPrimitiveCoordinates_iIndepFun {Seed : Type*} [MeasurableSpace Seed]
    (μ : Measure Seed) [IsProbabilityMeasure μ] (r : ℕ) :
    ProbabilityTheory.iIndepFun
      (fun i (t : MultilevelTree Seed (r + 1)) => multilevelPrimitiveCoordinates Seed r t i)
      (multilevelTreeLaw μ (r + 1)) := by
  have hp : MeasurePreserving (multilevelPrimitiveCoordinates Seed r)
      (multilevelTreeLaw μ (r + 1)) (Measure.pi (multilevelPrimitiveMeasure μ r)) :=
    multilevelTreeToPrimitive_measurePreserving μ r
  have hc (i : MultilevelPrimitiveIndex r) : MeasurePreserving
      (fun t : MultilevelTree Seed (r + 1) => multilevelPrimitiveCoordinates Seed r t i)
      (multilevelTreeLaw μ (r + 1)) (multilevelPrimitiveMeasure μ r i) :=
    (measurePreserving_eval (multilevelPrimitiveMeasure μ r) i).comp hp
  apply (ProbabilityTheory.iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (hc i).measurable.aemeasurable)).2
  change Measure.map (multilevelPrimitiveCoordinates Seed r) (multilevelTreeLaw μ (r + 1)) = _
  rw [hp.map_eq]
  congr 1
  funext i
  exact (hc i).map_eq.symm

end ProphetSecretary.Analysis
