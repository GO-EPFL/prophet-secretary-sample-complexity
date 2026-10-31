import ProphetSecretary.Limiting.ChronologicalHistoryCorrespondence
import ProphetSecretary.Limiting.ChronologicalPoissonPayload

/-!
# Conditional payload reconstruction from the observed Poisson past

Each observed point uses its chronological auxiliary sample. A fixed measurable
payload kernel therefore reconstructs a measurable tagged past, with exact
agreement with the actual per-count payload array. Current payloads use the
strict-past rank, and no total future count enters these observations.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

abbrev PayloadPoint (T : Type*) := ℝ × (ℝ × T)

def mapPayloadPoint {U T : Type*} (F : ℝ × U → ℝ × T) (p : PayloadPoint U) : PayloadPoint T := (p.1,F p.2)

lemma measurable_mapPayloadPoint {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    {F : ℝ × U → ℝ × T} (hF : Measurable F) : Measurable (mapPayloadPoint F) :=
  measurable_fst.prodMk (hF.comp measurable_snd)

noncomputable def conditionalPayloadHistory {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    (F : ℝ × U → ℝ × T) (u : ℕ → U) (H : FiniteMeasure Point) : Measure (PayloadPoint T) :=
  (chronologicalTaggedHistory u H).map (mapPayloadPoint F)

lemma measurable_conditionalPayloadHistory {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    {F : ℝ × U → ℝ × T} (hF : Measurable F) :
    Measurable (fun z : (ℕ → U) × FiniteMeasure Point => conditionalPayloadHistory F z.1 z.2) :=
  (Measure.measurable_map _ (measurable_mapPayloadPoint hF)).comp measurable_chronologicalTaggedHistory

noncomputable def payloadObservedHistory {T : Type*} [MeasurableSpace T]
    (ω : PayloadConfiguration T) (t : ℝ) : Measure (PayloadPoint T) :=
  ∑ j : Fin ω.1, if (ω.2 j).1<t then Measure.dirac (ω.2 j) else 0

lemma conditionalPayloadHistory_eq_array_past {U T : Type*} [MeasurableSpace U] [MeasurableSpace T]
    (F : ℝ × U → ℝ × T) (hF : Measurable F) (ω : Configuration) (u : ℕ → U)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1)) (t : ℝ) :
    conditionalPayloadHistory F u (observedFiniteHistory ω t)=
      payloadObservedHistory (chronologicalPayloadConfiguration F (ω,u)) t := by
  rw [conditionalPayloadHistory,chronologicalTaggedHistory_eq_array_past ω u hClock t]
  have hMap := measurable_mapPayloadPoint hF
  have hSum : (∑ j : Fin ω.1, if (ω.2 j).1<t then
      Measure.dirac ((ω.2 j).1,((ω.2 j).2,u (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val)) else 0).map
      (mapPayloadPoint F)=∑ j : Fin ω.1, (if (ω.2 j).1<t then
        Measure.dirac ((ω.2 j).1,((ω.2 j).2,u (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val)) else 0).map (mapPayloadPoint F) := by
    simp only [← Measure.mapₗ_apply_of_measurable hMap,map_sum]
  rw [chronologicalObservedTagHistory,hSum]
  unfold payloadObservedHistory chronologicalPayloadConfiguration
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : (ω.2 j).1<t
  · rw [if_pos hj,if_pos hj,Measure.map_dirac' hMap]
    rfl
  · rw [if_neg hj,if_neg hj,Measure.map_zero]

lemma conditionalCurrentPayload_eq_array {U T : Type*} (F : ℝ × U → ℝ × T)
    (ω : Configuration) (u : ℕ → U) (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1))
    (j : Fin ω.1) :
    F ((ω.2 j).2,u (finitePastRank (observedFiniteHistory ω (ω.2 j).1) (ω.2 j).1))=
      ((chronologicalPayloadConfiguration F (ω,u)).2 j).2 := by
  rw [finitePastRank_observedHistory ω hClock j le_rfl]
  rfl

def forgetPayloadPoint {T : Type*} (p : PayloadPoint T) : Point := (p.1,p.2.1)

lemma measurable_forgetPayloadPoint {T : Type*} [MeasurableSpace T] : Measurable (forgetPayloadPoint (T := T)) :=
  measurable_fst.prodMk measurable_snd.fst

lemma forget_chronologicalTaggedHistory {T : Type*} [MeasurableSpace T]
    (σ : ℕ → T) (H : FiniteMeasure Point) :
    (chronologicalTaggedHistory σ H).map forgetPayloadPoint=(H : Measure Point) := by
  have hTag : Measurable (tagPointByFiniteHistory σ H) :=
    measurable_tagPointByFiniteHistory.comp ((measurable_const (a := (σ,H))).prodMk measurable_id)
  rw [chronologicalTaggedHistory,Measure.map_map measurable_forgetPayloadPoint hTag]
  change (H : Measure Point).map id=(H : Measure Point)
  exact Measure.map_id

end ProphetSecretary.Limiting
