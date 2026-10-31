import ProphetSecretary.Limiting.CountableIndividualTagObservations
import ProphetSecretary.Limiting.CountableIndividualPayloadWorld

/-!
# Reconstructing a payload only when its value is observed

The current affected arrival supplies a reconstructed old value and tag.
After that arrival, its history entry supplies the same payload. Before the
arrival, the tag is replaced by a fixed default and no unseen displayed value
is evaluated by the callback.
-/

open MeasureTheory Set
open scoped Classical

namespace ProphetSecretary.Limiting.CountableInstance

variable {Seed U T : Type*}

def observedIndividualValue : Option Point → ℝ
  | none => 0
  | some p => p.2

private def payloadObservationEncode : Option Point → Unit ⊕ Point
  | none => Sum.inl ()
  | some p => Sum.inr p

lemma measurable_observedIndividualValue : Measurable observedIndividualValue := by
  have hEncode : Measurable payloadObservationEncode := Measurable.of_comap_le le_rfl
  have h := ((measurable_const : Measurable (fun _ : Unit => (0 : ℝ))).sumElim measurable_snd).comp hEncode
  convert h using 1
  funext o
  cases o <;> rfl

noncomputable def payloadTagAtHistory (i : ℕ) (F : ℝ × U → ℝ × T) (t0 : T)
    (u : U) (H : IndividualHistory) : T :=
  if H i=none then t0 else (F (observedIndividualValue (H i),u)).2

noncomputable def CountableRule.pullbackIndividualPayload (π : CountableRule (Seed × T))
    (i : ℕ) (F : ℝ × U → ℝ × T) (t0 : T) : CountableRule (Seed × U) where
  individual r t j x H ξ := π.individual
    (r.1,if j=i then (F (x,r.2)).2 else payloadTagAtHistory i F t0 r.2 H) t j
    (if j=i then (F (x,r.2)).1 else x) (mapSingleIndividualHistory i (fun y => (F (y,r.2)).1) H) ξ
  poisson r t x H ξ := π.poisson (r.1,payloadTagAtHistory i F t0 r.2 H) t x
    (mapSingleIndividualHistory i (fun y => (F (y,r.2)).1) H) ξ

variable [MeasurableSpace Seed] [MeasurableSpace U] [MeasurableSpace T]

lemma measurable_payloadTagAtHistory (i : ℕ) {F : ℝ × U → ℝ × T} (hF : Measurable F) (t0 : T) :
    Measurable (fun z : U × IndividualHistory => payloadTagAtHistory i F t0 z.1 z.2) := by
  have hNone : MeasurableSet {z : U × IndividualHistory | z.2 i=none} := Model.measurableSet_observation_none.preimage ((measurable_pi_apply i).comp measurable_snd)
  have hObserved : Measurable (fun z : U × IndividualHistory => observedIndividualValue (z.2 i)) :=
    measurable_observedIndividualValue.comp ((measurable_pi_apply i).comp measurable_snd)
  exact Measurable.ite hNone measurable_const
    ((measurable_snd.comp hF).comp (hObserved.prodMk measurable_fst))

lemma CountableRule.pullbackIndividualPayload_isMeasurable (π : CountableRule (Seed × T)) (hπ : π.IsMeasurable)
    (i : ℕ) {F : ℝ × U → ℝ × T} (hF : Measurable F) (t0 : T) :
    (π.pullbackIndividualPayload i F t0).IsMeasurable := by
  have hHistory : Measurable (fun z : (Seed × U) × IndividualHistory =>
      mapSingleIndividualHistory i (fun y => (F (y,z.1.2)).1) z.2) :=
    measurable_seededSingleIndividualHistory i (g := fun r : Seed × U => fun y => (F (y,r.2)).1)
      ((measurable_fst.comp hF).comp (measurable_snd.prodMk measurable_fst.snd))
  have hPast := measurable_payloadTagAtHistory i hF t0
  let W := (Seed × U) × (ℝ × (ℕ × (ℝ × (IndividualHistory × Measure Point))))
  have hCurrentPayload : Measurable (fun z : W => F (z.2.2.2.1,z.1.2)) :=
    hF.comp (measurable_snd.snd.snd.fst.prodMk measurable_fst.snd)
  have hCurrentValue : Measurable (fun z : W => if z.2.2.1=i then (F (z.2.2.2.1,z.1.2)).1 else z.2.2.2.1) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd.snd.fst measurable_const)
      hCurrentPayload.fst measurable_snd.snd.snd.fst
  have hCurrentTag : Measurable (fun z : W =>
      if z.2.2.1=i then (F (z.2.2.2.1,z.1.2)).2 else payloadTagAtHistory i F t0 z.1.2 z.2.2.2.2.1) :=
    Measurable.ite (measurableSet_eq_fun measurable_snd.snd.fst measurable_const) hCurrentPayload.snd
      (hPast.comp (measurable_fst.snd.prodMk measurable_snd.snd.snd.snd.fst))
  refine ⟨?_,?_⟩
  · exact hπ.1.comp ((measurable_fst.fst.prodMk hCurrentTag).prodMk (measurable_snd.fst.prodMk
      (measurable_snd.snd.fst.prodMk (hCurrentValue.prodMk
        ((hHistory.comp (measurable_fst.prodMk measurable_snd.snd.snd.snd.fst)).prodMk measurable_snd.snd.snd.snd.snd)))))
  · exact hπ.2.comp ((measurable_fst.fst.prodMk
      (hPast.comp (measurable_fst.snd.prodMk measurable_snd.snd.fst))).prodMk
      (measurable_snd.fst.prodMk
        ((hHistory.comp (measurable_fst.prodMk measurable_snd.snd.fst)).prodMk measurable_snd.snd.snd)))

end ProphetSecretary.Limiting.CountableInstance
