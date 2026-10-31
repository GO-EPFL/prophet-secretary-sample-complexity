import ProphetSecretary.Statistics.FiniteResponsePatching

/-!
# Fresh response samples and independent response seeds

The actual h+d training reservoir splits into independent preliminary h samples
and d response samples. Projecting a fixed component of the common seed product
then gives the exact independent input law of that response learner.
-/

open MeasureTheory Set Filter
open scoped Classical
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n h d : ℕ} {ι : Type} [Fintype ι]

noncomputable def responseTrainingIndexEquiv (n h d : ℕ) :
    ((Fin n × Fin h) ⊕ (Fin n × Fin d)) ≃ (Fin n × Fin (h+d)) :=
  (Equiv.prodSumDistrib (Fin n) (Fin h) (Fin d)).symm.trans
    (Equiv.prodCongr (Equiv.refl (Fin n)) finSumFinEquiv)

noncomputable def responseTrainingFlatSplit (n h d : ℕ) :
    ((Fin n × Fin (h+d)) → ℝ) ≃ᵐ (((Fin n × Fin h) → ℝ) × ((Fin n × Fin d) → ℝ)) :=
  (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin (h+d) => ℝ) (responseTrainingIndexEquiv n h d)).symm.trans
    (MeasurableEquiv.sumPiEquivProdPi (fun _ => ℝ))

noncomputable def responseTrainingSplit (n h d : ℕ) :
    Reservoir n (h+d) ≃ᵐ (((Fin n × Fin h) → ℝ) × Reservoir n d) :=
  reservoirCoordinates.trans ((responseTrainingFlatSplit n h d).trans
    ((MeasurableEquiv.refl ((Fin n × Fin h) → ℝ)).prodCongr reservoirCoordinates.symm))

lemma responseTrainingSplit_apply (y : Reservoir n (h+d)) :
    responseTrainingSplit n h d y=(preliminaryTrainingArray y,responseTrainingReservoir y) := rfl

lemma responseTrainingFlatSplit_measurePreserving (P : Instance n) (h d : ℕ) :
    MeasurePreserving (responseTrainingFlatSplit n h d) (P.trainingCoordinateLaw (h+d))
      ((P.trainingCoordinateLaw h).prod (P.trainingCoordinateLaw d)) := by
  let e := responseTrainingIndexEquiv n h d
  let μ := fun q : Fin n × Fin (h+d) => P.law q.1
  let μ' := fun q => μ (e q)
  haveI : ∀ q, IsProbabilityMeasure (μ' q) := fun q => P.probability (e q).1
  have h0 := (measurePreserving_piCongrLeft μ e).symm
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin (h+d) => ℝ) e)
  exact (measurePreserving_sumPiEquivProdPi μ').comp h0

lemma responseTrainingSplit_measurePreserving (P : Instance n) (h d : ℕ) :
    MeasurePreserving (responseTrainingSplit n h d) (P.reservoirLaw (h+d))
      ((P.trainingCoordinateLaw h).prod (P.reservoirLaw d)) :=
  ((MeasurePreserving.id (P.trainingCoordinateLaw h)).prod (P.reservoirCoordinates_symm_measurePreserving d)).comp
    ((responseTrainingFlatSplit_measurePreserving P h d).comp (P.reservoirCoordinates_measurePreserving (h+d)))

lemma fixedResponseInput_measurePreserving (P : Instance n) (L : ι → Learner n d) (c : ι) (h : ℕ) :
    MeasurePreserving (fun p : Reservoir n (h+d) × FiniteResponseSeeds L =>
      (preliminaryTrainingArray p.1,(responseTrainingReservoir p.1,p.2 c)))
      ((P.reservoirLaw (h+d)).prod (finiteResponseSeedLaw L))
      ((P.trainingCoordinateLaw h).prod ((P.reservoirLaw d).prod (L c).seedLaw)) := by
  have h0 := (responseTrainingSplit_measurePreserving P h d).prod (finiteResponseSeed_eval_measurePreserving L c)
  have h1 := measurePreserving_prodAssoc (P.trainingCoordinateLaw h) (P.reservoirLaw d) (L c).seedLaw
  exact h1.comp h0

end ProphetSecretary.Statistics
