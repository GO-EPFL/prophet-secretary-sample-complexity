import ProphetSecretary.Model.OuterRetention
import ProphetSecretary.Model.AllSamplesLearner
import ProphetSecretary.Model.TrainingCoordinates

/-!
# Actual full training rounds with free independent tags

A finite product-measure equivalence transposes the per-distribution reservoir
into full rounds. Independent uniform tags are then paired with each raw offer.
The causal full-sample transcript recovers exactly these rounds on every outcome,
with q requests per distribution and no extra sample cost for the tags.
-/

open MeasureTheory Set Filter
open scoped Classical BigOperators
namespace ProphetSecretary.Statistics
open ProphetSecretary.Model
variable {n q : ℕ}

def outerRoundCoordinates (n q : ℕ) : (Fin q → Fin n → ℝ) ≃ᵐ ((Fin n × Fin q) → ℝ) :=
  (MeasurableEquiv.curry (Fin q) (Fin n) ℝ).symm.trans
    (MeasurableEquiv.piCongrLeft (fun _ : Fin n × Fin q => ℝ) (Equiv.prodComm (Fin q) (Fin n)))

lemma outerRoundCoordinates_measurePreserving (P : Instance n) (q : ℕ) :
    MeasurePreserving (outerRoundCoordinates n q) (Measure.pi (fun _ : Fin q => P.valuesLaw)) (P.trainingCoordinateLaw q) := by
  have hm := (outerRoundCoordinates n q).measurable
  refine ⟨hm,?_⟩
  haveI : IsProbabilityMeasure ((Measure.pi (fun _ : Fin q => P.valuesLaw)).map (outerRoundCoordinates n q)) :=
    Measure.isProbabilityMeasure_map hm.aemeasurable
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hSet : outerRoundCoordinates n q ⁻¹' Set.univ.pi s=
      Set.univ.pi (fun r : Fin q => Set.univ.pi (fun i : Fin n => s (i,r))) := by
    ext a
    simp only [Set.mem_preimage,Set.mem_pi,Set.mem_univ,forall_true_left]
    exact ⟨fun h r i => h (i,r),fun h p => h p.2 p.1⟩
  rw [hSet,Measure.pi_pi]
  simp only [Instance.valuesLaw,Measure.pi_pi]
  rw [←Finset.univ_product_univ,Finset.prod_product]
  exact Finset.prod_comm

def outerTrainingRows (y : Reservoir n q) : Fin q → Fin n → ℝ := fun r i => y i r

lemma outerTrainingRows_measurePreserving (P : Instance n) (q : ℕ) :
    MeasurePreserving (outerTrainingRows (n:=n) (q:=q)) (P.reservoirLaw q) (Measure.pi (fun _ : Fin q => P.valuesLaw)) :=
  ((outerRoundCoordinates_measurePreserving P q).symm (outerRoundCoordinates n q)).comp (P.reservoirCoordinates_measurePreserving q)

noncomputable def outerTagRowsLaw (n q : ℕ) : Measure (Fin q → Fin n → ℝ) :=
  Measure.pi (fun _ : Fin q => Instance.clocksLaw n)

instance outerTagRowsLaw_probability (n q : ℕ) : IsProbabilityMeasure (outerTagRowsLaw n q) := by unfold outerTagRowsLaw;infer_instance

noncomputable def taggedTrainingRows (y : Reservoir n q) (tags : Fin q → Fin n → ℝ) : Fin q → Fin n → ℝ × ℝ :=
  fun r i => (y i r,tags r i)

lemma measurable_taggedTrainingRows : Measurable (fun p : Reservoir n q × (Fin q → Fin n → ℝ) => taggedTrainingRows p.1 p.2) := by
  apply measurable_pi_lambda
  intro r
  apply measurable_pi_lambda
  intro i
  have hValue : Measurable (fun p : Reservoir n q × (Fin q → Fin n → ℝ) => p.1 i r) :=
    (measurable_pi_apply r).comp ((measurable_pi_apply i).comp measurable_fst)
  have hTag : Measurable (fun p : Reservoir n q × (Fin q → Fin n → ℝ) => p.2 r i) :=
    (measurable_pi_apply i).comp ((measurable_pi_apply r).comp measurable_snd)
  exact hValue.prodMk hTag

lemma taggedTrainingRows_measurePreserving (P : Instance n) (q : ℕ) :
    MeasurePreserving (fun p : Reservoir n q × (Fin q → Fin n → ℝ) => taggedTrainingRows p.1 p.2)
      ((P.reservoirLaw q).prod (outerTagRowsLaw n q)) (Measure.pi (fun _ : Fin q => P.taggedValuesLaw)) := by
  have hOffer : MeasurePreserving (fun p : (Fin n → ℝ) × (Fin n → ℝ) => fun i => (p.1 i,p.2 i))
      (P.valuesLaw.prod (Instance.clocksLaw n)) P.taggedValuesLaw :=
    (measurePreserving_arrowProdEquivProdArrow ℝ ℝ (Fin n) P.law (fun _ => Instance.uniformClock)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow ℝ ℝ (Fin n))
  have hRowPair := (measurePreserving_arrowProdEquivProdArrow (Fin n → ℝ) (Fin n → ℝ) (Fin q)
    (fun _ => P.valuesLaw) (fun _ => Instance.clocksLaw n)).symm
      (MeasurableEquiv.arrowProdEquivProdArrow (Fin n → ℝ) (Fin n → ℝ) (Fin q))
  have hAll : MeasurePreserving (fun a : Fin q → ((Fin n → ℝ) × (Fin n → ℝ)) => fun r i => ((a r).1 i,(a r).2 i))
      (Measure.pi (fun _ : Fin q => P.valuesLaw.prod (Instance.clocksLaw n))) (Measure.pi (fun _ : Fin q => P.taggedValuesLaw)) := by
    refine ⟨measurable_pi_lambda _ (fun r => hOffer.measurable.comp (measurable_pi_apply r)),?_⟩
    rw [Measure.pi_map_pi (fun _ => hOffer.measurable.aemeasurable)]
    simp only [hOffer.map_eq]
  exact hAll.comp (hRowPair.comp ((outerTrainingRows_measurePreserving P q).prod (MeasurePreserving.id (outerTagRowsLaw n q))))

noncomputable def taggedRowsFromTranscript (tags : Fin q → Fin n → ℝ) (T : Transcript n) : Fin q → Fin n → ℝ × ℝ :=
  taggedTrainingRows (decodedReservoir T) tags

lemma measurable_taggedRowsFromTranscript : Measurable (fun p : (Fin q → Fin n → ℝ) × Transcript n => taggedRowsFromTranscript p.1 p.2) :=
  measurable_taggedTrainingRows.comp ((measurable_decodedReservoir.comp measurable_snd).prodMk measurable_fst)

lemma taggedRowsFromTranscript_actual (tags : Fin q → Fin n → ℝ) (y : Reservoir n q) :
    taggedRowsFromTranscript tags (trainingTranscript (requestAll q) tags y)=taggedTrainingRows y tags := by
  unfold taggedRowsFromTranscript
  rw [decodedReservoir_trainingTranscript]

lemma outerFullRounds_hardBudget (tags : Fin q → Fin n → ℝ) (y : Reservoir n q) (i : Fin n) :
    requests (trainingTranscript (requestAll q) tags y) i≤q := trainingTranscript_budget _ _ _ _

end ProphetSecretary.Statistics
