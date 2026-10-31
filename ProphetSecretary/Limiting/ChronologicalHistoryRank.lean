import ProphetSecretary.Limiting.ChronologicalHistoryTags
import ProphetSecretary.Limiting.ObservationRestrictions
import ProphetSecretary.Limiting.PoissonCounts
import ProphetSecretary.Limiting.CountableObservations
import ProphetSecretary.Probability.FiniteMeasureTotalization
import ProphetSecretary.Model.ArrivalRankTags

/-!
# Chronological rank from the actual observed point history

At an arriving point, its rank is the natural mass of the strict past. The
same rank is recovered from any later observed history. Thus independent
chronological tags can be reconstructed using only present observations.
-/

open MeasureTheory Set
open scoped Classical NNReal ENNReal

namespace ProphetSecretary.Limiting

instance observedHistory_isFinite (ω : Configuration) (t : ℝ) : IsFiniteMeasure (observedHistory ω t) := by
  unfold observedHistory
  haveI (j : Fin ω.1) : IsFiniteMeasure (if (ω.2 j).1<t then Measure.dirac (ω.2 j) else (0 : Measure Point)) := by
    split_ifs <;> infer_instance
  infer_instance

noncomputable def observedFiniteHistory (ω : Configuration) (t : ℝ) : FiniteMeasure Point :=
  ProphetSecretary.Probability.finiteMeasureOrZero (observedHistory ω t)

lemma observedFiniteHistory_coe (ω : Configuration) (t : ℝ) :
    (observedFiniteHistory ω t : Measure Point)=observedHistory ω t :=
  ProphetSecretary.Probability.finiteMeasureOrZero_coe _ inferInstance

lemma measurable_observedFiniteHistory :
    Measurable (fun z : Configuration × ℝ => observedFiniteHistory z.1 z.2) :=
  ProphetSecretary.Probability.measurable_finiteMeasureOrZero.comp CountableInstance.measurable_observedHistory_joint

lemma finitePastRank_observedHistory (ω : Configuration)
    (hClock : Function.Injective (fun j : Fin ω.1 => (ω.2 j).1))
    (j : Fin ω.1) {t : ℝ} (hjt : (ω.2 j).1≤t) :
    finitePastRank (observedFiniteHistory ω t) (ω.2 j).1=
      (Model.Instance.arrivalRank (fun k : Fin ω.1 => (ω.2 k).1) j).val := by
  have hZone : {p : Point | p.1<(ω.2 j).1}=Iio (ω.2 j).1 ×ˢ univ := by ext p; simp
  have hMeas : MeasurableSet (Iio (ω.2 j).1 ×ˢ (univ : Set ℝ)) := measurableSet_Iio.prod MeasurableSet.univ
  have hSub : Iio (ω.2 j).1 ×ˢ (univ : Set ℝ)⊆Iio t ×ˢ univ :=
    fun _ hp => ⟨hp.1.trans_le hjt,hp.2⟩
  unfold finitePastRank
  rw [hZone,Measure.real,observedFiniteHistory_coe,observedHistory_eq_countingRestriction,
    Measure.restrict_apply hMeas,inter_eq_left.mpr hSub,countingMeasure_eq_pointCount hMeas,
    ENNReal.toReal_natCast,Nat.floor_natCast]
  have h := Model.Instance.arrivalRank_counts_past hClock j
  simpa only [pointCount,Finset.card_filter,Set.mem_prod,Set.mem_Iio,Set.mem_univ,and_true] using h

end ProphetSecretary.Limiting
